//! C ABI over SLH-DSA-SHA2-128s verification (Arc PQ precompile, 0x1800…0004).
//!
//! One entry point. Lengths are NOT inferred: the caller passes exactly what the
//! precompile's ABI decode produced, and the length checks that precede parsing
//! live in the Lean spec (Evm.Arc.Spec.Pq) and its CL image, not here — so this
//! file has no policy in it at all, only the verification.

use slh_dsa::signature::Verifier;
use slh_dsa::{Sha2_128s, Signature, VerifyingKey};

/// Verify `sig` over `msg` under verifying key `vk`.
///
/// `vk` is `VK_LEN` = 32 bytes, `sig` is `SIG_LEN` = 7856 bytes; the caller has
/// already checked both lengths (they are separate, typed reverts in the
/// precompile, so they must not collapse into one code here).
///
/// Returns 1 valid, 0 invalid, -1 verifying key would not parse, -2 signature
/// would not parse, -3 a null pointer. The two parse codes are distinct because
/// the precompile reverts with different messages for them.
///
/// # Safety
/// `vk` must point to `vk_len` readable bytes, `sig` to `sig_len`, and `msg` to
/// `msg_len` (which may be 0, in which case `msg` is not read).
#[no_mangle]
pub unsafe extern "C" fn eita_slhdsa_sha2_128s_verify(
    vk: *const u8,
    vk_len: u64,
    msg: *const u8,
    msg_len: u64,
    sig: *const u8,
    sig_len: u64,
) -> i32 {
    if vk.is_null() || sig.is_null() || (msg.is_null() && msg_len != 0) {
        return -3;
    }
    let vk_bytes = std::slice::from_raw_parts(vk, vk_len as usize);
    let sig_bytes = std::slice::from_raw_parts(sig, sig_len as usize);
    let msg_bytes = if msg_len == 0 {
        &[][..]
    } else {
        std::slice::from_raw_parts(msg, msg_len as usize)
    };

    let key = match VerifyingKey::<Sha2_128s>::try_from(vk_bytes) {
        Ok(k) => k,
        Err(_) => return -1,
    };
    let signature = match Signature::<Sha2_128s>::try_from(sig_bytes) {
        Ok(s) => s,
        Err(_) => return -2,
    };
    if key.verify(msg_bytes, &signature).is_ok() {
        1
    } else {
        0
    }
}

/// Build guard: does the compiled parameter set really have Arc's 32-byte key and
/// 7856-byte signature? A SPHINCS+/SLH-DSA crate built for another parameter set
/// would otherwise surface 20 million blocks in as a "Failed to parse signature"
/// revert rather than as a load-time failure. Parse-only, so it costs nothing.
///
/// Returns 1 when both parse at Arc's lengths, 0 otherwise.
#[no_mangle]
pub extern "C" fn eita_slhdsa_sha2_128s_selftest() -> i32 {
    let vk = [0u8; 32];
    let sig = [0u8; 7856];
    let key_ok = VerifyingKey::<Sha2_128s>::try_from(&vk[..]).is_ok();
    let sig_ok = Signature::<Sha2_128s>::try_from(&sig[..]).is_ok();
    // And that a WRONG length is rejected, so the check cannot pass vacuously.
    let short_rejected = Signature::<Sha2_128s>::try_from(&sig[..7855]).is_err()
        && VerifyingKey::<Sha2_128s>::try_from(&vk[..31]).is_err();
    if key_ok && sig_ok && short_rejected { 1 } else { 0 }
}
