//! C ABI over Base's native precompiles (base/base `crates/common/precompiles` @ v1.5.6).
//!
//! One entry point, `eita_base_precompile`, runs the precompile at an address for a Base
//! upgrade, in the wrapper `base_precompile!` builds around every one of them
//! (`crates/common/precompiles/src/macros.rs:8-35`): a call that is not direct reverts with
//! `DelegateCallNotAllowed` at no gas, otherwise the body runs in `StorageCtx::enter` over a
//! storage provider with the upgrade's storage features. The bodies are the ones each
//! `precompile.rs` installs (b20_asset, b20_stablecoin, b20_factory, policy, activation,
//! tx_context, nonce); the address map is `BasePrecompiles::install_with_observer`
//! (`provider.rs:209-245`) and `BerylLookup` (`lookup.rs`).
//!
//! The provider here is the engine's: every operation the logic performs on the world is a
//! call back into the host (`HostFn`), which reads and writes the engine's world, journal,
//! access sets and transient storage and returns the operation's gas. This file holds no
//! gas number and no rule of its own: it forwards, deducts what the host priced, and keeps
//! the precompile's logs until it returns (a checkpoint revert drops the ones after it; a
//! failed call emits none).

use alloy_primitives::{Address, B256, Bytes, LogData, U256};
use base_common_chains::ChainConfig;
use base_common_genesis::BaseUpgrade;
use base_common_precompiles::{
    ActivationAdminConfig, ActivationRegistryStorage, B20AssetStorage, B20AssetToken,
    B20FactoryStorage, B20StablecoinStorage, B20StablecoinToken, B20Variant, NonceManagerStorage,
    NoopPrecompileCallObserver, PolicyRegistryStorage, PolicyVersions, TxContextStorage,
    UpgradeGatedStorageFeatures,
};
use base_precompile_storage::{
    BasePrecompileError, DelegateCallNotAllowed, PrecompileResult, PrecompileStatus,
    PrecompileStorageProvider, Result, StorageCtx, StorageFeatures,
};
use revm::{
    context::journaled_state::JournalCheckpoint,
    state::{AccountInfo, Bytecode},
};

/// The host: `(op, phase, a, b, c, n, out, aux) -> gas` (see the `OP_*` constants).
pub type HostFn = unsafe extern "C" fn(
    op: u32,
    phase: u32,
    a: *const u8,
    b: *const u8,
    c: *const u8,
    n: u64,
    out: *mut u8,
    aux: *mut i64,
) -> u64;

/// SLOAD: a = address (20), b = key (32) → out = value (32); gas.
const OP_SLOAD: u32 = 0;
/// SSTORE: a, b, c = value (32), n = gas left → *aux = refund delta; gas, or `u64::MAX`
/// when the EIP-2200 sentry refuses (nothing written).
const OP_SSTORE: u32 = 1;
/// TLOAD: a, b → out; gas (phase 1: unmetered, 0).
const OP_TLOAD: u32 = 2;
/// TSTORE: phase 0 → gas; phase 1: a, b, c → store.
const OP_TSTORE: u32 = 3;
/// Account: a → out = balance (32) ‖ nonce (8, big-endian) ‖ code hash (32); gas.
const OP_ACCOUNT: u32 = 4;
/// Code: phase 0: a → *aux = length; gas. Phase 1: copy the code into out (n bytes).
const OP_CODE: u32 = 5;
/// Install code: n = length. Phase 0 → deposit gas; phase 1: a → the new-code gas (0 when
/// the account has code); phase 2: a, b = code → install.
const OP_SET_CODE: u32 = 6;
/// Log gas: n = data length, *aux = topic count; gas.
const OP_LOG_GAS: u32 = 7;
/// Keccak gas: n = input length; gas.
const OP_KECCAK_GAS: u32 = 8;
/// Journal mark; returns it.
const OP_CHECKPOINT: u32 = 9;
/// Revert the journal to the mark n.
const OP_REVERT: u32 = 10;

/// The block and tx the precompile runs in (the provider's environment reads).
#[repr(C)]
pub struct Env {
    pub chain_id: u64,
    pub number: u64,
    pub timestamp: u64,
    pub beneficiary: [u8; 20],
    pub origin: [u8; 20],
}

/// The call's outcome. `status`: 0 success, 1 revert, 2 halt (out of gas); `out` is
/// owned by the shim until `eita_base_free`.
#[repr(C)]
pub struct Outcome {
    pub status: u32,
    pub gas_used: u64,
    pub refund: i64,
    pub out: *mut u8,
    pub out_len: u64,
    /// The precompile's logs, packed: per log address (20) ‖ topic count (1) ‖ topics ‖
    /// data length (8, big-endian) ‖ data. Emitted by the host on success only.
    pub logs: *mut u8,
    pub logs_len: u64,
}

struct Host {
    host: HostFn,
    env: Env,
    caller: Address,
    value: U256,
    is_static: bool,
    features: StorageFeatures,
    limit: u64,
    used: u64,
    refunded: i64,
    logs: Vec<(Address, LogData)>,
    checkpoints: Vec<(u64, usize)>,
}

impl Host {
    fn call(&self, op: u32, phase: u32, a: &[u8], b: &[u8], c: &[u8], n: u64, out: &mut [u8], aux: &mut i64) -> u64 {
        unsafe {
            (self.host)(op, phase, a.as_ptr(), b.as_ptr(), c.as_ptr(), n, out.as_mut_ptr(), aux as *mut i64)
        }
    }
    fn charge(&mut self, gas: u64) -> Result<()> {
        // revm Gas::record_regular_cost: the cost must fit in what is left
        if gas > self.limit - self.used {
            return Err(BasePrecompileError::OutOfGas);
        }
        self.used += gas;
        Ok(())
    }
}

impl PrecompileStorageProvider for Host {
    fn chain_id(&self) -> u64 { self.env.chain_id }
    fn timestamp(&self) -> U256 { U256::from(self.env.timestamp) }
    fn beneficiary(&self) -> Address { Address::from(self.env.beneficiary) }
    fn block_number(&self) -> u64 { self.env.number }
    fn origin(&self) -> Address { Address::from(self.env.origin) }

    fn set_code(&mut self, address: Address, code: Bytecode) -> Result<()> {
        if self.is_static {
            return Err(BasePrecompileError::StaticCallViolation);
        }
        // evm.rs set_code: the code deposit, then (an account without code) the CREATE cost
        // and the code hash's keccak, then the install
        let bytes = code.original_bytes();
        let mut aux = 0i64;
        let deposit = self.call(OP_SET_CODE, 0, &[], &[], &[], bytes.len() as u64, &mut [], &mut aux);
        self.charge(deposit)?;
        let extra = self.call(OP_SET_CODE, 1, address.as_slice(), &[], &[], bytes.len() as u64, &mut [], &mut aux);
        self.charge(extra)?;
        self.call(OP_SET_CODE, 2, address.as_slice(), &bytes, &[], bytes.len() as u64, &mut [], &mut aux);
        Ok(())
    }

    fn with_account_info(&mut self, address: Address, f: &mut dyn FnMut(&AccountInfo)) -> Result<()> {
        let mut out = [0u8; 72];
        let mut aux = 0i64;
        let gas = self.call(OP_ACCOUNT, 0, address.as_slice(), &[], &[], 0, &mut out, &mut aux);
        self.charge(gas)?;
        let mut info = AccountInfo::default();
        info.balance = U256::from_be_slice(&out[0..32]);
        info.nonce = u64::from_be_bytes(out[32..40].try_into().unwrap());
        info.code_hash = B256::from_slice(&out[40..72]);
        f(&info);
        Ok(())
    }

    fn with_account_code(&mut self, address: Address, f: &mut dyn FnMut(&Bytecode)) -> Result<()> {
        let mut aux = 0i64;
        let gas = self.call(OP_CODE, 0, address.as_slice(), &[], &[], 0, &mut [], &mut aux);
        let mut code = vec![0u8; aux as usize];
        self.call(OP_CODE, 1, address.as_slice(), &[], &[], code.len() as u64, &mut code, &mut aux);
        self.charge(gas)?;
        f(&Bytecode::new_raw(Bytes::from(code)));
        Ok(())
    }

    fn sload(&mut self, address: Address, key: U256) -> Result<U256> {
        let mut out = [0u8; 32];
        let mut aux = 0i64;
        let gas = self.call(OP_SLOAD, 0, address.as_slice(), &key.to_be_bytes::<32>(), &[], 0, &mut out, &mut aux);
        self.charge(gas)?;
        Ok(U256::from_be_bytes(out))
    }

    fn tload(&mut self, address: Address, key: U256) -> Result<U256> {
        let mut out = [0u8; 32];
        let mut aux = 0i64;
        let gas = self.call(OP_TLOAD, 0, address.as_slice(), &key.to_be_bytes::<32>(), &[], 0, &mut out, &mut aux);
        self.charge(gas)?;
        Ok(U256::from_be_bytes(out))
    }

    fn tload_unmetered(&mut self, address: Address, key: U256) -> Result<U256> {
        let mut out = [0u8; 32];
        let mut aux = 0i64;
        self.call(OP_TLOAD, 1, address.as_slice(), &key.to_be_bytes::<32>(), &[], 0, &mut out, &mut aux);
        Ok(U256::from_be_bytes(out))
    }

    fn sstore(&mut self, address: Address, key: U256, value: U256) -> Result<()> {
        if self.is_static {
            return Err(BasePrecompileError::StaticCallViolation);
        }
        let mut aux = 0i64;
        let gas = self.call(OP_SSTORE, 0, address.as_slice(), &key.to_be_bytes::<32>(),
                            &value.to_be_bytes::<32>(), self.limit - self.used, &mut [], &mut aux);
        if gas == u64::MAX {
            return Err(BasePrecompileError::OutOfGas);
        }
        // evm.rs sstore: the write and its cost are one checkpoint (an out-of-gas write is
        // undone with the call); the refund only when it is paid
        self.charge(gas)?;
        self.refunded += aux;
        Ok(())
    }

    fn tstore(&mut self, address: Address, key: U256, value: U256) -> Result<()> {
        if self.is_static {
            return Err(BasePrecompileError::StaticCallViolation);
        }
        let mut aux = 0i64;
        let gas = self.call(OP_TSTORE, 0, &[], &[], &[], 0, &mut [], &mut aux);
        self.charge(gas)?;
        self.call(OP_TSTORE, 1, address.as_slice(), &key.to_be_bytes::<32>(), &value.to_be_bytes::<32>(), 0, &mut [], &mut aux);
        Ok(())
    }

    fn emit_event(&mut self, address: Address, event: LogData) -> Result<()> {
        if self.is_static {
            return Err(BasePrecompileError::StaticCallViolation);
        }
        let mut aux = event.topics().len() as i64;
        let gas = self.call(OP_LOG_GAS, 0, &[], &[], &[], event.data.len() as u64, &mut [], &mut aux);
        self.charge(gas)?;
        self.logs.push((address, event));
        Ok(())
    }

    fn deduct_gas(&mut self, gas: u64) -> Result<()> { self.charge(gas) }
    fn deduct_state_gas(&mut self, gas: u64) -> Result<()> { self.charge(gas) }
    fn refund_gas(&mut self, gas: i64) { self.refunded += gas; }
    fn gas_limit(&self) -> u64 { self.limit }
    fn gas_used(&self) -> u64 { self.used }
    fn state_gas_used(&self) -> u64 { 0 }
    fn gas_refunded(&self) -> i64 { self.refunded }
    fn reservoir(&self) -> u64 { 0 }
    fn storage_features(&self) -> StorageFeatures { self.features }
    fn is_static(&self) -> bool { self.is_static }
    fn call_value(&self) -> U256 { self.value }
    fn caller(&self) -> Address { self.caller }
    fn replace_caller(&mut self, caller: Address) -> Address { core::mem::replace(&mut self.caller, caller) }

    fn checkpoint(&mut self) -> JournalCheckpoint {
        let mut aux = 0i64;
        let mark = self.call(OP_CHECKPOINT, 0, &[], &[], &[], 0, &mut [], &mut aux);
        self.checkpoints.push((mark, self.logs.len()));
        JournalCheckpoint { log_i: self.logs.len(), journal_i: mark as usize, selfdestructed_i: 0 }
    }

    fn commit_latest_checkpoint(&mut self) {
        self.checkpoints.pop();
    }

    fn checkpoint_revert(&mut self, checkpoint: JournalCheckpoint) {
        let mut aux = 0i64;
        self.call(OP_REVERT, 0, &[], &[], &[], checkpoint.journal_i as u64, &mut [], &mut aux);
        self.logs.truncate(checkpoint.log_i);
        while let Some(&(m, _)) = self.checkpoints.last() {
            self.checkpoints.pop();
            if m as usize == checkpoint.journal_i { break; }
        }
    }

    fn metered_keccak256(&mut self, data: &[u8]) -> Result<B256> {
        let mut aux = 0i64;
        let gas = self.call(OP_KECCAK_GAS, 0, &[], &[], &[], data.len() as u64, &mut [], &mut aux);
        self.charge(gas)?;
        Ok(alloy_primitives::keccak256(data))
    }
}

/// The Base upgrade by the engine's OP-fork ordinal (Evm.Optimism.OpFork.ord: 9 Beryl,
/// 10 Cobalt, 11 Denim). `None` before Beryl (no native precompile).
fn upgrade_of(op_fork: u32) -> Option<BaseUpgrade> {
    match op_fork {
        9 => Some(BaseUpgrade::Beryl),
        10 => Some(BaseUpgrade::Cobalt),
        11 => Some(BaseUpgrade::Denim),
        _ => None,
    }
}

/// Which native precompile `addr` is at `upgrade` (provider.rs:209-245, lookup.rs), as the
/// kind the engine's classification (Evm.Optimism.Beryl.Spec.nativeKind) must agree with:
/// 1 factory, 2 policy registry, 3 activation registry, 4 asset token, 5 stablecoin token,
/// 6 transaction context, 7 nonce manager; 0 none.
fn kind_of(addr: Address, upgrade: BaseUpgrade) -> u32 {
    if addr == B20FactoryStorage::ADDRESS { return 1; }
    if addr == PolicyRegistryStorage::ADDRESS { return 2; }
    if addr == ActivationRegistryStorage::ADDRESS { return 3; }
    if upgrade >= BaseUpgrade::Cobalt {
        if addr == TxContextStorage::ADDRESS { return 6; }
        if addr == NonceManagerStorage::ADDRESS { return 7; }
    }
    match B20Variant::from_address(addr) {
        Some(B20Variant::Asset) => 4,
        Some(B20Variant::Stablecoin) => 5,
        None => 0,
    }
}

/// The native-precompile kind of `addr` at OP fork `op_fork` (see `kind_of`); 0 when none.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn eita_base_precompile_kind(addr: *const u8, op_fork: u32) -> u32 {
    let addr = Address::from_slice(unsafe { std::slice::from_raw_parts(addr, 20) });
    upgrade_of(op_fork).map_or(0, |u| kind_of(addr, u))
}

fn body(ctx: StorageCtx<'_>, kind: u32, addr: Address, upgrade: BaseUpgrade, chain_id: u64, calldata: &[u8]) -> PrecompileResult {
    let obs = NoopPrecompileCallObserver;
    match kind {
        1 => B20FactoryStorage::new(ctx).dispatch_with_observer(ctx, calldata, upgrade, obs),
        2 => PolicyRegistryStorage::new(ctx).dispatch_with_observer(ctx, calldata, upgrade, obs),
        3 => {
            // provider.rs:230-238: the chain's configured admin (config.rs:325-333), read from
            // storage first from Cobalt
            let admin = ActivationAdminConfig::new(
                ChainConfig::beryl_activation_admin_address_by_chain_id(chain_id),
                upgrade >= BaseUpgrade::Cobalt,
            );
            ActivationRegistryStorage::new(ctx).dispatch_with_observer(ctx, calldata, admin, upgrade, obs)
        }
        4 | 5 => {
            let Some(version) = PolicyVersions::from_base_upgrade(upgrade) else {
                return BasePrecompileError::Revert(Bytes::new()).into_precompile_result(0, 0);
            };
            if kind == 4 {
                B20AssetToken::with_storage_and_policy(
                    B20AssetStorage::from_address(addr, ctx), PolicyRegistryStorage::new(ctx), version)
                .dispatch_with_observer(ctx, calldata, upgrade, obs)
            } else {
                B20StablecoinToken::with_storage_and_policy(
                    B20StablecoinStorage::from_address(addr, ctx), PolicyRegistryStorage::new(ctx), version)
                .dispatch_with_observer(ctx, calldata, upgrade, obs)
            }
        }
        6 => TxContextStorage::new(ctx).dispatch(ctx, calldata),
        7 => NonceManagerStorage::new(ctx).dispatch(ctx, calldata),
        _ => unreachable!(),
    }
}

fn leak(v: Vec<u8>) -> (*mut u8, u64) {
    let mut b = v.into_boxed_slice();
    let (p, n) = (b.as_mut_ptr(), b.len() as u64);
    std::mem::forget(b);
    (p, n)
}

/// Run the native precompile at `addr` (20 bytes) at OP fork `op_fork` for `caller` with
/// `value` (32 bytes), `input`, `gas`. `direct` is 0 for a DELEGATECALL or CALLCODE. Returns
/// 0 and fills `outcome`; -1 when `addr` is not a native precompile at the fork; -2 on a
/// fatal error (its message in `outcome.out`).
///
/// # Safety
/// Pointers must be valid for their lengths; `host` must follow the `OP_*` contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn eita_base_precompile(
    host: HostFn,
    env: *const Env,
    op_fork: u32,
    addr: *const u8,
    caller: *const u8,
    value: *const u8,
    is_static: u32,
    direct: u32,
    input: *const u8,
    input_len: u64,
    gas: u64,
    outcome: *mut Outcome,
) -> i32 {
    let (addr, caller, value, calldata, env) = unsafe {
        (Address::from_slice(std::slice::from_raw_parts(addr, 20)),
         Address::from_slice(std::slice::from_raw_parts(caller, 20)),
         U256::from_be_slice(std::slice::from_raw_parts(value, 32)),
         if input_len == 0 { &[][..] } else { std::slice::from_raw_parts(input, input_len as usize) },
         &*env)
    };
    let Some(upgrade) = upgrade_of(op_fork) else { return -1 };
    let kind = kind_of(addr, upgrade);
    if kind == 0 {
        return -1;
    }
    let result = if direct == 0 {
        // macros.rs:13-19
        BasePrecompileError::revert(DelegateCallNotAllowed {}).into_precompile_result(0, 0)
    } else {
        let mut h = Host {
            host,
            env: Env { chain_id: env.chain_id, number: env.number, timestamp: env.timestamp,
                       beneficiary: env.beneficiary, origin: env.origin },
            caller, value, is_static: is_static != 0,
            features: UpgradeGatedStorageFeatures::from_upgrade(upgrade),
            limit: gas, used: 0, refunded: 0, logs: Vec::new(), checkpoints: Vec::new(),
        };
        let r = StorageCtx::enter(&mut h, |ctx| body(ctx, kind, addr, upgrade, env.chain_id, calldata));
        if let Ok(o) = &r {
            if o.is_success() {
                let mut packed = Vec::new();
                for (a, log) in &h.logs {
                    packed.extend_from_slice(a.as_slice());
                    packed.push(log.topics().len() as u8);
                    for t in log.topics() { packed.extend_from_slice(t.as_slice()); }
                    packed.extend_from_slice(&(log.data.len() as u64).to_be_bytes());
                    packed.extend_from_slice(&log.data);
                }
                let (p, n) = leak(packed);
                unsafe { (*outcome).logs = p; (*outcome).logs_len = n; }
            }
        }
        r
    };
    let o = unsafe { &mut *outcome };
    match result {
        Ok(out) => {
            o.status = match out.status {
                PrecompileStatus::Success => 0,
                PrecompileStatus::Revert => 1,
                PrecompileStatus::Halt(_) => 2,
            };
            // precompile_provider.rs:92-112 (revm-handler 42): a halt, or a claim above the
            // limit, spends it all and returns nothing
            if o.status == 2 || out.gas_used > gas {
                o.status = 2;
                o.gas_used = gas;
                o.refund = 0;
                o.out = std::ptr::null_mut();
                o.out_len = 0;
            } else {
                o.gas_used = out.gas_used;
                o.refund = if o.status == 0 { out.gas_refunded } else { 0 };
                let (p, n) = leak(out.bytes.to_vec());
                o.out = p;
                o.out_len = n;
            }
            0
        }
        Err(e) => {
            let (p, n) = leak(format!("{e:?}").into_bytes());
            o.out = p;
            o.out_len = n;
            -2
        }
    }
}

/// Free a buffer `eita_base_precompile` returned.
///
/// # Safety
/// `p`/`n` must come from one `Outcome` field pair, freed once.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn eita_base_free(p: *mut u8, n: u64) {
    if !p.is_null() {
        drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(p, n as usize)) });
    }
}
