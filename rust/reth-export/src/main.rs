//! eita-reth-export: a reth datadir's current state as an Eita record stream.
//!
//!   eita-reth-export --datadir DIR --chain-id N > state.stream
//!   eita-reth-export --datadir DIR --chain-id N | eita import-reth --state STATE-DIR -
//!
//! Opens DIR/db (MDBX) and DIR/static_files read-only. The state is read from reth's hashed
//! tables, `HashedAccounts` (keccak(address) -> account) and `HashedStorages` (keccak(address)
//! -> keccak(slot) -> value), which every reth layout keeps and which reth's "storage v2"
//! (Base's snapshots) keeps as its only current state: v2 writes no plain-address tables. Both
//! tables are in the trie's key order, which is snapshot format v2's order
//! (docs/state-snapshot-format.md), so the export is one walk of each, merged, with no sort and
//! no trie. Codes come from `Bytecodes` (by code hash, code.dat's order). reth's trie tables
//! and stored roots are never read: `eita import-reth` recomputes the root from these records
//! and compares it with the header's.
//!
//! The block H is the one the state belongs to: the Finish stage's checkpoint. A database
//! whose state is persisted only partly past some block (Finish's `partial_state_trie`) is
//! refused. H's header (from the static files) gives the hash and the stateRoot.
//!
//! The stream (big-endian, as the snapshot files):
//!   "EITARETH" · version u32 = 1 · chain-id u64 · block u64 · hash 32 · state-root 32
//!     · accounts u64 · slots u64 (the tables' entry counts: the writer's size estimate)
//!     · provenance-len u16 · provenance (UTF-8)
//!   then, per account in keccak(address) order, its slots, then the account:
//!   'S' · a 96-byte v2 slot record (haddr · hslot · value)
//!   'A' · a 128-byte v2 account record (hkey · addr · flags · nonce · balance · codehash);
//!         addr is 20 zero bytes: the hashed tables hold no address (format v2 §3)
//!   then every code in code-hash order:
//!   'C' · codehash 32 · len u32 · bytes
//!   'E' · accounts u64 · slots u64 · codes u64 (what was written)

use alloy_primitives::{keccak256, B256, KECCAK256_EMPTY};
use eyre::{bail, eyre, Result};
use reth_db::{open_db_read_only, mdbx::DatabaseArguments, tables};
use reth_db_api::{
    cursor::DbCursorRO,
    database::Database,
    transaction::DbTx,
};
use reth_ethereum_primitives::EthPrimitives;
use reth_provider::{providers::StaticFileProvider, HeaderProvider};
use reth_stages_types::StageId;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

const RETH_REV: &str = "base/reth@2b20e42de9c4";
const FLAG_EXISTS: u32 = 1;

fn main() -> Result<()> {
    let mut datadir = None;
    let mut chain_id = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--datadir" => datadir = args.next().map(PathBuf::from),
            "--chain-id" => chain_id = args.next().and_then(|s| s.parse::<u64>().ok()),
            _ => bail!("usage: eita-reth-export --datadir DIR --chain-id N  (unknown argument {a})"),
        }
    }
    let (Some(datadir), Some(chain_id)) = (datadir, chain_id) else {
        bail!("usage: eita-reth-export --datadir DIR --chain-id N");
    };

    let db = open_db_read_only(datadir.join("db"), DatabaseArguments::default())?;
    let tx = db.tx()?;

    let finish = tx
        .get::<tables::StageCheckpoints>(StageId::Finish.to_string())?
        .ok_or_else(|| eyre!("no Finish stage checkpoint: not a synced reth database"))?;
    // A partial_state_trie below the Finish block means blocks past it are only partly
    // persisted: the hashed tables then match no block (seen on a dev node stopped with
    // SIGINT). reth repairs it at startup by unwinding to that block, so start the node on the
    // datadir once (no consensus client: it does not advance), stop it, and export again.
    let block = finish.block_number;
    if let Some(p) = finish.finish_stage_checkpoint().and_then(|f| f.partial_state_trie()) {
        if p < block {
            bail!(
                "the state is persisted only partly past block {p} (Finish is at {block}): \
                 start the node on this datadir once, stop it, and export again"
            );
        }
    }
    let settings = tx
        .get::<tables::Metadata>("storage_settings".to_string())?
        .map(|v| String::from_utf8_lossy(&v).into_owned())
        .unwrap_or_else(|| "(none: v1)".into());

    let sf = StaticFileProvider::<EthPrimitives>::read_only(datadir.join("static_files"))?;
    let header = sf.header_by_number(block)?.ok_or_else(|| eyre!("no header {block} in the static files"))?;
    let hash = header.hash_slow();
    let state_root = header.state_root;

    let count = |name: &str| -> Result<u64> {
        let t = tx.inner().open_db(Some(name))?;
        Ok(tx.inner().db_stat(t.dbi())?.entries() as u64)
    };
    let (n_acct, n_slot) = (count("HashedAccounts")?, count("HashedStorages")?);
    eprintln!(
        "reth-export: block {block} hash {hash} stateRoot {state_root}; finish checkpoint {}, \
         storage settings {settings}; {n_acct} accounts, {n_slot} slots",
        finish.block_number
    );

    let provenance = format!("imported reth {RETH_REV} @ block {block} ({hash})");
    let mut out = BufWriter::with_capacity(1 << 22, std::io::stdout().lock());
    out.write_all(b"EITARETH")?;
    out.write_all(&1u32.to_be_bytes())?;
    out.write_all(&chain_id.to_be_bytes())?;
    out.write_all(&block.to_be_bytes())?;
    out.write_all(hash.as_slice())?;
    out.write_all(state_root.as_slice())?;
    out.write_all(&n_acct.to_be_bytes())?;
    out.write_all(&n_slot.to_be_bytes())?;
    out.write_all(&(provenance.len() as u16).to_be_bytes())?;
    out.write_all(provenance.as_bytes())?;

    // Accounts and slots: both cursors move forward together. Every slot's account comes
    // right after its slots (S5: a slot whose haddr has no account is an error).
    let mut accts = tx.cursor_read::<tables::HashedAccounts>()?;
    let mut slots = tx.cursor_dup_read::<tables::HashedStorages>()?;
    let mut codes = tx.cursor_read::<tables::Bytecodes>()?;
    let mut slot = slots.first()?;
    let (mut wa, mut ws, mut wc) = (0u64, 0u64, 0u64);
    let mut rec = [0u8; 128];
    let mut a = accts.first()?;
    while let Some((hkey, acct)) = a {
        while let Some((haddr, entry)) = slot {
            if haddr > hkey {
                break;
            }
            if haddr < hkey {
                bail!("storage of {haddr} without an account (S5)");
            }
            if entry.value.is_zero() {
                bail!("a zero slot {haddr}/{} (S2)", entry.key);
            }
            out.write_all(b"S")?;
            out.write_all(haddr.as_slice())?;
            out.write_all(entry.key.as_slice())?;
            out.write_all(&entry.value.to_be_bytes::<32>())?;
            ws += 1;
            slot = slots.next()?;
        }
        let codehash = acct.bytecode_hash.unwrap_or(KECCAK256_EMPTY);
        if codehash != KECCAK256_EMPTY && codes.seek_exact(codehash)?.is_none() {
            bail!("account {hkey}: code {codehash} is not in Bytecodes (S3)");
        }
        let empty = acct.nonce == 0 && acct.balance.is_zero() && codehash == KECCAK256_EMPTY;
        rec.fill(0);
        rec[0..32].copy_from_slice(hkey.as_slice());
        // rec[32..52]: the address, unknown here
        rec[52..56].copy_from_slice(&(if empty { FLAG_EXISTS } else { 0 }).to_be_bytes());
        rec[56..64].copy_from_slice(&acct.nonce.to_be_bytes());
        rec[64..96].copy_from_slice(&acct.balance.to_be_bytes::<32>());
        rec[96..128].copy_from_slice(codehash.as_slice());
        out.write_all(b"A")?;
        out.write_all(&rec)?;
        wa += 1;
        if wa % 10_000_000 == 0 {
            eprintln!("reth-export: {wa} accounts, {ws} slots");
        }
        a = accts.next()?;
    }
    if let Some((haddr, _)) = slot {
        bail!("storage of {haddr} after the last account (S5)");
    }

    let mut c = codes.first()?;
    while let Some((h, code)) = c {
        let bytes = code.original_bytes();
        let got: B256 = keccak256(&bytes);
        if got != h {
            bail!("Bytecodes: the code under {h} hashes to {got}");
        }
        if h != KECCAK256_EMPTY {
            out.write_all(b"C")?;
            out.write_all(h.as_slice())?;
            out.write_all(&(bytes.len() as u32).to_be_bytes())?;
            out.write_all(&bytes)?;
            wc += 1;
        }
        c = codes.next()?;
    }
    out.write_all(b"E")?;
    for n in [wa, ws, wc] {
        out.write_all(&n.to_be_bytes())?;
    }
    out.flush()?;
    eprintln!("reth-export: wrote {wa} accounts, {ws} slots, {wc} codes for block {block}");
    Ok(())
}
