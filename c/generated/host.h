/* c/generated/host.h — EMITTED by `lake exe emitHostC` from lean/Evm/CL/GasEmitC.lean;
   do not edit. Each function is the C printing of the same Evm.CL.GasEmit term that
   src/generated/host.lisp prints as Common Lisp, so a C host and the Lisp host compute
   one formula, owned by Lean. Regenerate, never hand-edit (CONTRIBUTING rule 2). */
#ifndef EITA_GENERATED_HOST_H
#define EITA_GENERATED_HOST_H
#include <stdint.h>

void eita_spec_overflow(const char *where) __attribute__((noreturn));

/* Held back for the 256-bit printer (wei-valued: not bounded by the gas limit,
   and their intermediates exceed 2^64 — see Evm.CL.GasEmitC.Dom):
     spec-block-base-reward
     spec-uncle-inclusion-bonus
     spec-uncle-reward
     spec-blob-base-fee
     spec-effective-gas-price
   src/generated/host.lisp emits all of them. */

/* SHA2-256 precompile (0x02) */
uint64_t eita_spec_sha256_gas(uint64_t len);
uint64_t eita_spec_ripemd160_gas(uint64_t len);
uint64_t eita_spec_identity_gas(uint64_t len);
uint64_t eita_spec_ecrecover_gas(void);
uint64_t eita_spec_p256verify_gas(void);
uint64_t eita_spec_rip7212_gas(void);
uint64_t eita_spec_point_evaluation_gas(void);
uint64_t eita_spec_auth_intrinsic_per_auth(void);
uint64_t eita_spec_auth_refund_existing(void);
uint64_t eita_spec_bn256_add_gas(uint64_t fork_ord);
uint64_t eita_spec_bn256_mul_gas(uint64_t fork_ord);
uint64_t eita_spec_bn256_pairing_gas(uint64_t len, uint64_t fork_ord);
uint64_t eita_spec_bls_g1add_gas(void);
uint64_t eita_spec_bls_g2add_gas(void);
uint64_t eita_spec_bls_map_fp_to_g1_gas(void);
uint64_t eita_spec_bls_map_fp2_to_g2_gas(void);
uint64_t eita_spec_bls_pairing_gas(uint64_t len);
/* EELS calculate_intrinsic_cost (+ EIP-2930 access list, EIP-3860 initcode words) */
uint64_t eita_spec_intrinsic_gas(uint64_t is_create, uint64_t data_len, uint64_t zero_bytes, uint64_t nonzero_bytes, uint64_t al_addrs, uint64_t al_keys, uint64_t fork_ord);
uint64_t eita_spec_code_deposit_gas(uint64_t nbytes);
uint64_t eita_spec_create_gas(uint64_t fork_ord, uint64_t is_create2, uint64_t initcode_len);
/* EIP-3860 initcode cap */
uint64_t eita_spec_create_initcode_oversize(uint64_t fork_ord, uint64_t initcode_len);
uint64_t eita_spec_selfdestruct_refund(uint64_t fork_ord);
/* EIP-7623 */
uint64_t eita_spec_calldata_floor_gas(uint64_t zero_bytes, uint64_t nonzero_bytes, uint64_t fork_ord);
uint64_t eita_spec_tx_gas_used(uint64_t gas_used, uint64_t refund_counter, uint64_t zero_bytes, uint64_t nonzero_bytes, uint64_t fork_ord);
/* EIP-2929 */
uint64_t eita_spec_selfdestruct_cold_gas(uint64_t cold);
/* EIP-7702 */
uint64_t eita_spec_delegate_access_gas(uint64_t cold);
uint64_t eita_spec_retain_63_64(uint64_t gas, uint64_t fork_ord);
uint64_t eita_spec_new_account_fee(void);
/* account access + value surcharge + new-account fee, by fork */
uint64_t eita_spec_call_extra_gas(uint64_t cold, uint64_t value_nonzero, uint64_t new_acct, uint64_t fork_ord);
/* EIP-150 CALL stipend, added to the sub-frame */
uint64_t eita_spec_call_stipend_gas(uint64_t value_nonzero);
uint64_t eita_spec_max_blob_gas_per_block(uint64_t fork_ord);
/* EIP-7825 (Osaka+) */
uint64_t eita_spec_tx_max_gas_limit(void);
/* MODEXP (0x05): EIP-198 pre-Berlin / EIP-2565 Berlin+ / EIP-7883 Osaka+ */
uint64_t eita_spec_modexp_gas(uint64_t base_sz, uint64_t exp_sz, uint64_t mod_sz, const uint64_t *exp_head, uint64_t fork_ord);
/* Ethereum mainnet fork schedule (Evm.Forks.ofBlock) */
uint64_t eita_spec_mainnet_fork_ord(uint64_t n, uint64_t ts);

#endif
