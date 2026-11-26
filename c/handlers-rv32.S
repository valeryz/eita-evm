.text
.globl eita_run
.p2align 2
eita_run:
    addi sp, sp, -64
    sw   ra, 0(sp)
    sw   s0, 4(sp)
    sw   s1, 8(sp)
    sw   s2, 12(sp)
    sw   s3, 16(sp)
    sw   s4, 20(sp)
    sw   s5, 24(sp)
    sw   s6, 28(sp)
    sw   s7, 32(sp)
    sw   s8, 36(sp)
    sw   s9, 40(sp)
    sw   s10, 44(sp)
    sw   s11, 48(sp)
    mv   s0, a0
    lw   s1, 0(a0)
    lw   s5, 8(a0)
    lw   t0, 12(a0)
    bnez t0, eita_gas_too_wide
    lw   s2, 16(a0)
    slli s2, s2, 5
    lw   s3, 32(a0)
    lw   s4, 64(a0)
    sw   sp, 544(s0)
    li   t0, 0
    la   t0, eita_dispatch_ptr
    lw   t0, 0(t0)
    sw   t0, 600(s0)
    beqz s2, .Lrun_nocache
    add  t0, s3, s2
    lw   a0, -32(t0)
    lw   a1, -28(t0)
    lw   a2, -24(t0)
    lw   a3, -20(t0)
    lw   a4, -16(t0)
    lw   a5, -12(t0)
    lw   a6, -8(t0)
    lw   a7, -4(t0)
.Lrun_nocache:
.globl eita_next
eita_next:
    add  t0, s4, s1
    lbu  t0, 0(t0)
    addi s1, s1, 1
    lw   t1, 600(s0)
    slli t0, t0, 2
    add  t1, t1, t0
    lw   t1, 0(t1)
    jalr t1
    j    eita_next
.globl eita_sync_and_ret
.p2align 2
eita_sync_and_ret:
    lw   sp, 544(s0)
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    srli t0, s2, 5
    sw   t0, 16(s0)
    sw   zero, 20(s0)
    beqz s2, .Lsync_nostack
    add  t0, s3, s2
    sw   a0, -32(t0)
    sw   a1, -28(t0)
    sw   a2, -24(t0)
    sw   a3, -20(t0)
    sw   a4, -16(t0)
    sw   a5, -12(t0)
    sw   a6, -8(t0)
    sw   a7, -4(t0)
.Lsync_nostack:
    lw   ra, 0(sp)
    lw   s0, 4(sp)
    lw   s1, 8(sp)
    lw   s2, 12(sp)
    lw   s3, 16(sp)
    lw   s4, 20(sp)
    lw   s5, 24(sp)
    lw   s6, 28(sp)
    lw   s7, 32(sp)
    lw   s8, 36(sp)
    lw   s9, 40(sp)
    lw   s10, 44(sp)
    lw   s11, 48(sp)
    addi sp, sp, 64
    ret
.globl eita_oog
.p2align 2
eita_oog:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.globl eita_stack_overflow
.p2align 2
eita_stack_overflow:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.globl eita_stack_underflow
.p2align 2
eita_stack_underflow:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.globl eita_static_violation
.p2align 2
eita_static_violation:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.globl eita_invalid_jump
.p2align 2
eita_invalid_jump:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.globl eita_gas_too_wide
.p2align 2
eita_gas_too_wide:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.globl eita_unimplemented
.p2align 2
eita_unimplemented:
    lw   sp, 544(s0)
    li   s5, 0
    li   t0, 1
    sb   t0, 128(s0)
    sb   t0, 129(s0)
    j    eita_sync_and_ret
.text
.globl eita_set_fork
.p2align 2
eita_set_fork:
    li   t0, 21
    bgeu t0, a0, .Lsf_ok
    mv   a0, t0
.Lsf_ok:
    la   t1, eita_fork_tables
    slli a0, a0, 2
    add  t1, t1, a0
    lw   t1, 0(t1)
    la   t2, eita_dispatch_ptr
    sw   t1, 0(t2)
    ret
.data
.globl eita_dispatch_table_frontier
.p2align 2
eita_dispatch_table_frontier:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_unimplemented
.data
.globl eita_dispatch_table_homestead
.p2align 2
eita_dispatch_table_homestead:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_unimplemented
.data
.globl eita_dispatch_table_dao_fork
.p2align 2
eita_dispatch_table_dao_fork:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_unimplemented
.data
.globl eita_dispatch_table_tangerine_whistle
.p2align 2
eita_dispatch_table_tangerine_whistle:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_spurious_dragon
.p2align 2
eita_dispatch_table_spurious_dragon:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_byzantium
.p2align 2
eita_dispatch_table_byzantium:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_invalid
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_constantinople
.p2align 2
eita_dispatch_table_constantinople:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_petersburg
.p2align 2
eita_dispatch_table_petersburg:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_unimplemented
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_istanbul
.p2align 2
eita_dispatch_table_istanbul:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_muir_glacier
.p2align 2
eita_dispatch_table_muir_glacier:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_berlin
.p2align 2
eita_dispatch_table_berlin:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_london
.p2align 2
eita_dispatch_table_london:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_arrow_glacier
.p2align 2
eita_dispatch_table_arrow_glacier:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_gray_glacier
.p2align 2
eita_dispatch_table_gray_glacier:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_paris
.p2align 2
eita_dispatch_table_paris:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_shanghai
.p2align 2
eita_dispatch_table_shanghai:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_push0
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table
.p2align 2
eita_dispatch_table:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_blobhash
    .word   eita_handler_blobbasefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_tload
    .word   eita_handler_tstore
    .word   eita_handler_mcopy
    .word   eita_handler_push0
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_dispatch_table_osaka
.p2align 2
eita_dispatch_table_osaka:
    .word   eita_handler_stop
    .word   eita_handler_add
    .word   eita_handler_mul
    .word   eita_handler_sub
    .word   eita_handler_div
    .word   eita_handler_sdiv
    .word   eita_handler_mod
    .word   eita_handler_smod
    .word   eita_handler_addmod
    .word   eita_handler_mulmod
    .word   eita_unimplemented
    .word   eita_handler_signextend
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_lt
    .word   eita_handler_gt
    .word   eita_unimplemented
    .word   eita_unimplemented
    .word   eita_handler_eq
    .word   eita_handler_iszero
    .word   eita_handler_and
    .word   eita_handler_or
    .word   eita_handler_xor
    .word   eita_handler_not
    .word   eita_handler_byte
    .word   eita_handler_shl
    .word   eita_handler_shr
    .word   eita_handler_sar
    .word   eita_unimplemented
    .word   eita_handler_invalid
    .word   eita_handler_keccak256
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_address
    .word   eita_handler_balance
    .word   eita_handler_origin
    .word   eita_handler_caller
    .word   eita_handler_callvalue
    .word   eita_handler_calldataload
    .word   eita_handler_calldatasize
    .word   eita_handler_calldatacopy
    .word   eita_handler_codesize
    .word   eita_handler_codecopy
    .word   eita_handler_gasprice
    .word   eita_handler_extcodesize
    .word   eita_handler_extcodecopy
    .word   eita_handler_returndatasize
    .word   eita_handler_returndatacopy
    .word   eita_handler_extcodehash
    .word   eita_handler_blockhash
    .word   eita_handler_coinbase
    .word   eita_handler_timestamp
    .word   eita_handler_number
    .word   eita_handler_prevrandao
    .word   eita_handler_gaslimit
    .word   eita_handler_chainid
    .word   eita_handler_selfbalance
    .word   eita_handler_basefee
    .word   eita_handler_blobhash
    .word   eita_handler_blobbasefee
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_pop
    .word   eita_handler_mload
    .word   eita_handler_mstore
    .word   eita_handler_mstore8
    .word   eita_handler_sload
    .word   eita_handler_sstore
    .word   eita_handler_jump
    .word   eita_handler_jumpi
    .word   eita_handler_pc
    .word   eita_handler_msize
    .word   eita_handler_gas
    .word   eita_handler_jumpdest
    .word   eita_handler_tload
    .word   eita_handler_tstore
    .word   eita_handler_mcopy
    .word   eita_handler_push0
    .word   eita_handler_push1
    .word   eita_handler_push2
    .word   eita_handler_push3
    .word   eita_handler_push4
    .word   eita_handler_push5
    .word   eita_handler_push6
    .word   eita_handler_push7
    .word   eita_handler_push8
    .word   eita_handler_push9
    .word   eita_handler_push10
    .word   eita_handler_push11
    .word   eita_handler_push12
    .word   eita_handler_push13
    .word   eita_handler_push14
    .word   eita_handler_push15
    .word   eita_handler_push16
    .word   eita_handler_push17
    .word   eita_handler_push18
    .word   eita_handler_push19
    .word   eita_handler_push20
    .word   eita_handler_push21
    .word   eita_handler_push22
    .word   eita_handler_push23
    .word   eita_handler_push24
    .word   eita_handler_push25
    .word   eita_handler_push26
    .word   eita_handler_push27
    .word   eita_handler_push28
    .word   eita_handler_push29
    .word   eita_handler_push30
    .word   eita_handler_push31
    .word   eita_handler_push32
    .word   eita_handler_dup1
    .word   eita_handler_dup2
    .word   eita_handler_dup3
    .word   eita_handler_dup4
    .word   eita_handler_dup5
    .word   eita_handler_dup6
    .word   eita_handler_dup7
    .word   eita_handler_dup8
    .word   eita_handler_dup9
    .word   eita_handler_dup10
    .word   eita_handler_dup11
    .word   eita_handler_dup12
    .word   eita_handler_dup13
    .word   eita_handler_dup14
    .word   eita_handler_dup15
    .word   eita_handler_dup16
    .word   eita_handler_swap1
    .word   eita_handler_swap2
    .word   eita_handler_swap3
    .word   eita_handler_swap4
    .word   eita_handler_swap5
    .word   eita_handler_swap6
    .word   eita_handler_swap7
    .word   eita_handler_swap8
    .word   eita_handler_swap9
    .word   eita_handler_swap10
    .word   eita_handler_swap11
    .word   eita_handler_swap12
    .word   eita_handler_swap13
    .word   eita_handler_swap14
    .word   eita_handler_swap15
    .word   eita_handler_swap16
    .word   eita_handler_log0
    .word   eita_handler_log1
    .word   eita_handler_log2
    .word   eita_handler_log3
    .word   eita_handler_log4
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_create
    .word   eita_handler_call
    .word   eita_handler_callcode
    .word   eita_handler_return
    .word   eita_handler_delegatecall
    .word   eita_handler_create2
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_staticcall
    .word   eita_handler_invalid
    .word   eita_handler_invalid
    .word   eita_handler_revert
    .word   eita_handler_invalid
    .word   eita_handler_selfdestruct
.data
.globl eita_fork_tables
.p2align 2
eita_fork_tables:
    .word   eita_dispatch_table_frontier
    .word   eita_dispatch_table_homestead
    .word   eita_dispatch_table_dao_fork
    .word   eita_dispatch_table_tangerine_whistle
    .word   eita_dispatch_table_spurious_dragon
    .word   eita_dispatch_table_byzantium
    .word   eita_dispatch_table_constantinople
    .word   eita_dispatch_table_petersburg
    .word   eita_dispatch_table_istanbul
    .word   eita_dispatch_table_muir_glacier
    .word   eita_dispatch_table_berlin
    .word   eita_dispatch_table_london
    .word   eita_dispatch_table_arrow_glacier
    .word   eita_dispatch_table_gray_glacier
    .word   eita_dispatch_table_paris
    .word   eita_dispatch_table_shanghai
    .word   eita_dispatch_table
    .word   eita_dispatch_table
    .word   eita_dispatch_table_osaka
    .word   eita_dispatch_table_osaka
    .word   eita_dispatch_table_osaka
    .word   eita_dispatch_table_osaka
.globl eita_dispatch_ptr
.p2align 2
eita_dispatch_ptr:
    .word   eita_dispatch_table
.text
.globl eita_handler_add
.p2align 2
eita_handler_add:
    li   s7, 64
    bnez zero, .Lx0
    bltu s2, s7, eita_stack_underflow
.Lx0:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  a0, a0, s6
    sltu s7, a0, s6
    add  a1, a1, s7
    sltu s7, a1, s7
    add  a1, a1, t6
    bgeu a1, t6, .Lk3
    addi s7, s7, 1
.Lk3:
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    add  a2, a2, s7
    sltu s7, a2, s7
    add  a2, a2, s6
    bgeu a2, s6, .Lk4
    addi s7, s7, 1
.Lk4:
    add  a3, a3, s7
    sltu s7, a3, s7
    add  a3, a3, t6
    bgeu a3, t6, .Lk5
    addi s7, s7, 1
.Lk5:
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    add  a4, a4, s7
    sltu s7, a4, s7
    add  a4, a4, s6
    bgeu a4, s6, .Lk6
    addi s7, s7, 1
.Lk6:
    add  a5, a5, s7
    sltu s7, a5, s7
    add  a5, a5, t6
    bgeu a5, t6, .Lk7
    addi s7, s7, 1
.Lk7:
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    add  a6, a6, s7
    sltu s7, a6, s7
    add  a6, a6, s6
    bgeu a6, s6, .Lk8
    addi s7, s7, 1
.Lk8:
    add  a7, a7, s7
    add  a7, a7, t6
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_sub
.p2align 2
eita_handler_sub:
    li   s7, 64
    bnez zero, .Lx34
    bltu s2, s7, eita_stack_underflow
.Lx34:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    sltu s7, a0, s6
    sub  a0, a0, s6
    sw   t0, 608(s0)
    sltu t0, a1, s7
    sub  a1, a1, s7
    sltu s7, a1, t6
    sub  a1, a1, t6
    or   s7, s7, t0
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    sw   t0, 608(s0)
    sltu t0, a2, s7
    sub  a2, a2, s7
    sltu s7, a2, s6
    sub  a2, a2, s6
    or   s7, s7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sltu t0, a3, s7
    sub  a3, a3, s7
    sltu s7, a3, t6
    sub  a3, a3, t6
    or   s7, s7, t0
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    sw   t0, 608(s0)
    sltu t0, a4, s7
    sub  a4, a4, s7
    sltu s7, a4, s6
    sub  a4, a4, s6
    or   s7, s7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sltu t0, a5, s7
    sub  a5, a5, s7
    sltu s7, a5, t6
    sub  a5, a5, t6
    or   s7, s7, t0
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    sw   t0, 608(s0)
    sltu t0, a6, s7
    sub  a6, a6, s7
    sltu s7, a6, s6
    sub  a6, a6, s6
    or   s7, s7, t0
    lw   t0, 608(s0)
    sub  a7, a7, t6
    sub  a7, a7, s7
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_and
.p2align 2
eita_handler_and:
    li   s7, 64
    bnez zero, .Lx68
    bltu s2, s7, eita_stack_underflow
.Lx68:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    and  a0, a0, s6
    and  a1, a1, t6
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    and  a2, a2, s6
    and  a3, a3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    and  a4, a4, s6
    and  a5, a5, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    and  a6, a6, s6
    and  a7, a7, t6
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_or
.p2align 2
eita_handler_or:
    li   s7, 64
    bnez zero, .Lx102
    bltu s2, s7, eita_stack_underflow
.Lx102:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   a0, a0, s6
    or   a1, a1, t6
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    or   a2, a2, s6
    or   a3, a3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   a4, a4, s6
    or   a5, a5, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   a6, a6, s6
    or   a7, a7, t6
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_xor
.p2align 2
eita_handler_xor:
    li   s7, 64
    bnez zero, .Lx136
    bltu s2, s7, eita_stack_underflow
.Lx136:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    xor  a0, a0, s6
    xor  a1, a1, t6
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    xor  a2, a2, s6
    xor  a3, a3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    xor  a4, a4, s6
    xor  a5, a5, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    xor  a6, a6, s6
    xor  a7, a7, t6
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_lt
.p2align 2
eita_handler_lt:
    li   s7, 64
    bnez zero, .Lx170
    bltu s2, s7, eita_stack_underflow
.Lx170:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    sw   t0, 616(s0)
    sltu s7, a0, s6
    sub  t0, a0, s6
    sw   t1, 608(s0)
    sltu t1, a1, s7
    sub  t0, a1, s7
    sltu s7, t0, t6
    sub  t0, t0, t6
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    sw   t0, 616(s0)
    sw   t1, 608(s0)
    sltu t1, a2, s7
    sub  t0, a2, s7
    sltu s7, t0, s6
    sub  t0, t0, s6
    or   s7, s7, t1
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sltu t1, a3, s7
    sub  t0, a3, s7
    sltu s7, t0, t6
    sub  t0, t0, t6
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    sw   t0, 616(s0)
    sw   t1, 608(s0)
    sltu t1, a4, s7
    sub  t0, a4, s7
    sltu s7, t0, s6
    sub  t0, t0, s6
    or   s7, s7, t1
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sltu t1, a5, s7
    sub  t0, a5, s7
    sltu s7, t0, t6
    sub  t0, t0, t6
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    sw   t0, 616(s0)
    sw   t1, 608(s0)
    sltu t1, a6, s7
    sub  t0, a6, s7
    sltu s7, t0, s6
    sub  t0, t0, s6
    or   s7, s7, t1
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sltu t1, a7, s7
    sub  t0, a7, s7
    sltu s7, t0, t6
    sub  t0, t0, t6
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    mv   a0, s7
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_gt
.p2align 2
eita_handler_gt:
    li   s7, 64
    bnez zero, .Lx212
    bltu s2, s7, eita_stack_underflow
.Lx212:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    sw   t0, 616(s0)
    sltu s7, s6, a0
    sub  t0, s6, a0
    sw   t1, 608(s0)
    sltu t1, t6, s7
    sub  t0, t6, s7
    sltu s7, t0, a1
    sub  t0, t0, a1
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    sw   t0, 616(s0)
    sw   t1, 608(s0)
    sltu t1, s6, s7
    sub  t0, s6, s7
    sltu s7, t0, a2
    sub  t0, t0, a2
    or   s7, s7, t1
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sltu t1, t6, s7
    sub  t0, t6, s7
    sltu s7, t0, a3
    sub  t0, t0, a3
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    sw   t0, 616(s0)
    sw   t1, 608(s0)
    sltu t1, s6, s7
    sub  t0, s6, s7
    sltu s7, t0, a4
    sub  t0, t0, a4
    or   s7, s7, t1
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sltu t1, t6, s7
    sub  t0, t6, s7
    sltu s7, t0, a5
    sub  t0, t0, a5
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    sw   t0, 616(s0)
    sw   t1, 608(s0)
    sltu t1, s6, s7
    sub  t0, s6, s7
    sltu s7, t0, a6
    sub  t0, t0, a6
    or   s7, s7, t1
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sltu t1, t6, s7
    sub  t0, t6, s7
    sltu s7, t0, a7
    sub  t0, t0, a7
    or   s7, s7, t1
    lw   t1, 608(s0)
    lw   t0, 616(s0)
    mv   a0, s7
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_eq
.p2align 2
eita_handler_eq:
    li   s7, 64
    bnez zero, .Lx254
    bltu s2, s7, eita_stack_underflow
.Lx254:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    xor  t2, a0, s6
    xor  t3, a1, t6
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    xor  t4, a2, s6
    xor  t5, a3, t6
    or   t2, t2, t4
    or   t3, t3, t5
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    xor  t4, a4, s6
    xor  t5, a5, t6
    or   t2, t2, t4
    or   t3, t3, t5
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    xor  t4, a6, s6
    xor  t5, a7, t6
    or   t2, t2, t4
    or   t3, t3, t5
    li   s7, 0
    bnez t3, .Lne262
    bne  t2, s7, .Lne262
    li   a0, 1
    li   a1, 0
    j    .Lsd262
.Lne262:
    li   a0, 0
    li   a1, 0
.Lsd262:
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_iszero
.p2align 2
eita_handler_iszero:
    li   s7, 32
    bnez zero, .Lx304
    bltu s2, s7, eita_stack_underflow
.Lx304:
    or   t2, a0, a2
    or   t3, a1, a3
    or   t4, a4, a6
    or   t5, a5, a7
    or   t2, t2, t4
    or   t3, t3, t5
    li   s7, 0
    bnez t3, .Lne308
    bne  t2, s7, .Lne308
    li   a0, 1
    li   a1, 0
    j    .Lsd308
.Lne308:
    li   a0, 0
    li   a1, 0
.Lsd308:
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_not
.p2align 2
eita_handler_not:
    li   s7, 32
    bnez zero, .Lx340
    bltu s2, s7, eita_stack_underflow
.Lx340:
    not  a0, a0
    not  a1, a1
    not  a2, a2
    not  a3, a3
    not  a4, a4
    not  a5, a5
    not  a6, a6
    not  a7, a7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_pop
.p2align 2
eita_handler_pop:
    li   s7, 32
    bnez zero, .Lx368
    bltu s2, s7, eita_stack_underflow
.Lx368:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   a0, s6
    mv   a1, t6
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   a2, s6
    mv   a3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    mv   a4, s6
    mv   a5, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    mv   a6, s6
    mv   a7, t6
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_stop
.p2align 2
eita_handler_stop:
    sltiu s7, s1, 1
    addi s1, s1, -1
    sub  zero, zero, s7
    li   t2, 1
    li   t3, 0
    sb   t2, 128(s0)
    j    eita_sync_and_ret
.text
.globl eita_handler_jumpdest
.p2align 2
eita_handler_jumpdest:
    sltiu s7, s5, 1
    addi s5, s5, -1
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_invalid
.p2align 2
eita_handler_invalid:
    j    eita_oog
.text
.globl eita_handler_address
.p2align 2
eita_handler_address:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 144(s0)
    lw   a1, 148(s0)
    lw   a2, 152(s0)
    lw   a3, 156(s0)
    lw   a4, 160(s0)
    lw   a5, 164(s0)
    lw   a6, 168(s0)
    lw   a7, 172(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_origin
.p2align 2
eita_handler_origin:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 176(s0)
    lw   a1, 180(s0)
    lw   a2, 184(s0)
    lw   a3, 188(s0)
    lw   a4, 192(s0)
    lw   a5, 196(s0)
    lw   a6, 200(s0)
    lw   a7, 204(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_caller
.p2align 2
eita_handler_caller:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 208(s0)
    lw   a1, 212(s0)
    lw   a2, 216(s0)
    lw   a3, 220(s0)
    lw   a4, 224(s0)
    lw   a5, 228(s0)
    lw   a6, 232(s0)
    lw   a7, 236(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_coinbase
.p2align 2
eita_handler_coinbase:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 336(s0)
    lw   a1, 340(s0)
    lw   a2, 344(s0)
    lw   a3, 348(s0)
    lw   a4, 352(s0)
    lw   a5, 356(s0)
    lw   a6, 360(s0)
    lw   a7, 364(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_callvalue
.p2align 2
eita_handler_callvalue:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 240(s0)
    lw   a1, 244(s0)
    lw   a2, 248(s0)
    lw   a3, 252(s0)
    lw   a4, 256(s0)
    lw   a5, 260(s0)
    lw   a6, 264(s0)
    lw   a7, 268(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_gasprice
.p2align 2
eita_handler_gasprice:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 272(s0)
    lw   a1, 276(s0)
    lw   a2, 280(s0)
    lw   a3, 284(s0)
    lw   a4, 288(s0)
    lw   a5, 292(s0)
    lw   a6, 296(s0)
    lw   a7, 300(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_chainid
.p2align 2
eita_handler_chainid:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 304(s0)
    lw   a1, 308(s0)
    lw   a2, 312(s0)
    lw   a3, 316(s0)
    lw   a4, 320(s0)
    lw   a5, 324(s0)
    lw   a6, 328(s0)
    lw   a7, 332(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_timestamp
.p2align 2
eita_handler_timestamp:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 368(s0)
    lw   a1, 372(s0)
    lw   a2, 376(s0)
    lw   a3, 380(s0)
    lw   a4, 384(s0)
    lw   a5, 388(s0)
    lw   a6, 392(s0)
    lw   a7, 396(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_number
.p2align 2
eita_handler_number:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 400(s0)
    lw   a1, 404(s0)
    lw   a2, 408(s0)
    lw   a3, 412(s0)
    lw   a4, 416(s0)
    lw   a5, 420(s0)
    lw   a6, 424(s0)
    lw   a7, 428(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_gaslimit
.p2align 2
eita_handler_gaslimit:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 432(s0)
    lw   a1, 436(s0)
    lw   a2, 440(s0)
    lw   a3, 444(s0)
    lw   a4, 448(s0)
    lw   a5, 452(s0)
    lw   a6, 456(s0)
    lw   a7, 460(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_basefee
.p2align 2
eita_handler_basefee:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 464(s0)
    lw   a1, 468(s0)
    lw   a2, 472(s0)
    lw   a3, 476(s0)
    lw   a4, 480(s0)
    lw   a5, 484(s0)
    lw   a6, 488(s0)
    lw   a7, 492(s0)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_prevrandao
.p2align 2
eita_handler_prevrandao:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    addi t2, s0, 512
    sltiu s7, t2, 512
    add  t3, zero, s7
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_blobhash
.p2align 2
eita_handler_blobhash:
    li   s7, 32
    bnez zero, .Lx730
    bltu s2, s7, eita_stack_underflow
.Lx730:
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, .Lbh_zero
    lw   t2, 560(s0)
    lw   t3, 564(s0)
    bltu a1, t3, .Lx735
    bne  t3, a1, .Lbh_zero
    bgeu a0, t2, .Lbh_zero
.Lx735:
    lw   t4, 552(s0)
    lw   t5, 556(s0)
    slli t6, a1, 5
    srli s7, a0, 27
    or   t6, t6, s7
    slli s6, a0, 5
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t2)
    lbu  t0, 1(t2)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t2)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t2)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t2)
    lbu  t0, 5(t2)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t2)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t2)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  a4, 16(t2)
    lbu  t0, 17(t2)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 18(t2)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 19(t2)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 20(t2)
    lbu  t0, 21(t2)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 22(t2)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 23(t2)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  a6, 24(t2)
    lbu  t0, 25(t2)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 26(t2)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 27(t2)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 28(t2)
    lbu  t0, 29(t2)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 30(t2)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 31(t2)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    j    .Lbh_done
.Lbh_zero:
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
.Lbh_done:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_blobbasefee
.p2align 2
eita_handler_blobbasefee:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    addi t2, s0, 568
    sltiu s7, t2, 568
    add  t3, zero, s7
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_pc
.p2align 2
eita_handler_pc:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    sltiu s7, s1, 1
    addi a0, s1, -1
    sub  a1, zero, s7
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_msize
.p2align 2
eita_handler_msize:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 48(s0)
    lw   a1, 52(s0)
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_gas
.p2align 2
eita_handler_gas:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    mv   a0, s5
    mv   a1, zero
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    ret
.text
.globl eita_handler_calldatasize
.p2align 2
eita_handler_calldatasize:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 88(s0)
    lw   a1, 92(s0)
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_codesize
.p2align 2
eita_handler_codesize:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 72(s0)
    lw   a1, 76(s0)
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_returndatasize
.p2align 2
eita_handler_returndatasize:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    lw   a0, 104(s0)
    lw   a1, 108(s0)
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_sstore
.p2align 2
eita_handler_sstore:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 64
    bnez zero, .Lx994
    bltu s2, s7, eita_stack_underflow
.Lx994:
    li   t2, 2300
    li   t3, 0
    bltu t3, zero, .Lx996
    bne  zero, t3, eita_oog
    bgeu t2, s5, eita_oog
.Lx996:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   a0, 504(s0)
    addi a1, s0, 144
    addi a2, s2, -32
    add  a2, s3, a2
    addi a3, s2, -64
    add  a3, s3, a3
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 12(t0)
    lw   t0, 8(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t2, 504(s0)
    lw   t3, 508(s0)
    sw   t0, 608(s0)
    lbu  t4, 0(t2)
    lbu  t0, 1(t2)
    slli t0, t0, 8
    or   t4, t4, t0
    lbu  t0, 2(t2)
    slli t0, t0, 16
    or   t4, t4, t0
    lbu  t0, 3(t2)
    slli t0, t0, 24
    or   t4, t4, t0
    lbu  t5, 4(t2)
    lbu  t0, 5(t2)
    slli t0, t0, 8
    or   t5, t5, t0
    lbu  t0, 6(t2)
    slli t0, t0, 16
    or   t5, t5, t0
    lbu  t0, 7(t2)
    slli t0, t0, 24
    or   t5, t5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  s10, 16(t2)
    lbu  t0, 17(t2)
    slli t0, t0, 8
    or   s10, s10, t0
    lbu  t0, 18(t2)
    slli t0, t0, 16
    or   s10, s10, t0
    lbu  t0, 19(t2)
    slli t0, t0, 24
    or   s10, s10, t0
    lbu  s11, 20(t2)
    lbu  t0, 21(t2)
    slli t0, t0, 8
    or   s11, s11, t0
    lbu  t0, 22(t2)
    slli t0, t0, 16
    or   s11, s11, t0
    lbu  t0, 23(t2)
    slli t0, t0, 24
    or   s11, s11, t0
    lw   t0, 608(s0)
    li   s8, 104
    li   s9, 0
    mulhu t1, t4, s8
    mul  t0, t4, s8
    mul  s7, t4, s9
    add  t1, t1, s7
    mul  s7, t5, s8
    add  t1, t1, s7
    add  t0, t0, s10
    sltu s7, t0, s10
    add  t1, t1, s11
    add  t1, t1, s7
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    sb   t4, 0(t2)
    srli t0, t4, 8
    sb   t0, 1(t2)
    srli t0, t4, 16
    sb   t0, 2(t2)
    srli t0, t4, 24
    sb   t0, 3(t2)
    sb   t5, 4(t2)
    srli t0, t5, 8
    sb   t0, 5(t2)
    srli t0, t5, 16
    sb   t0, 6(t2)
    srli t0, t5, 24
    sb   t0, 7(t2)
    lw   t0, 608(s0)
    sb   zero, 0(t0)
    srli zero, zero, 8
    sb   zero, 1(t0)
    srli zero, zero, 16
    sb   zero, 2(t0)
    srli zero, zero, 24
    sb   zero, 3(t0)
    sb   zero, 4(t0)
    srli zero, zero, 8
    sb   zero, 5(t0)
    srli zero, zero, 16
    sb   zero, 6(t0)
    srli zero, zero, 24
    sb   zero, 7(t0)
    lw   t4, 144(s0)
    lw   t5, 148(s0)
    lw   s8, 152(s0)
    lw   s9, 156(s0)
    sw   t1, 608(s0)
    sb   t4, 8(t0)
    srli t1, t4, 8
    sb   t1, 9(t0)
    srli t1, t4, 16
    sb   t1, 10(t0)
    srli t1, t4, 24
    sb   t1, 11(t0)
    sb   t5, 12(t0)
    srli t1, t5, 8
    sb   t1, 13(t0)
    srli t1, t5, 16
    sb   t1, 14(t0)
    srli t1, t5, 24
    sb   t1, 15(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   s8, 16(t0)
    srli t1, s8, 8
    sb   t1, 17(t0)
    srli t1, s8, 16
    sb   t1, 18(t0)
    srli t1, s8, 24
    sb   t1, 19(t0)
    sb   s9, 20(t0)
    srli t1, s9, 8
    sb   t1, 21(t0)
    srli t1, s9, 16
    sb   t1, 22(t0)
    srli t1, s9, 24
    sb   t1, 23(t0)
    lw   t1, 608(s0)
    lw   s10, 160(s0)
    lw   s11, 164(s0)
    lw   s8, 168(s0)
    lw   s9, 172(s0)
    sw   t1, 608(s0)
    sb   s10, 24(t0)
    srli t1, s10, 8
    sb   t1, 25(t0)
    srli t1, s10, 16
    sb   t1, 26(t0)
    srli t1, s10, 24
    sb   t1, 27(t0)
    sb   s11, 28(t0)
    srli t1, s11, 8
    sb   t1, 29(t0)
    srli t1, s11, 16
    sb   t1, 30(t0)
    srli t1, s11, 24
    sb   t1, 31(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   s8, 32(t0)
    srli t1, s8, 8
    sb   t1, 33(t0)
    srli t1, s8, 16
    sb   t1, 34(t0)
    srli t1, s8, 24
    sb   t1, 35(t0)
    sb   s9, 36(t0)
    srli t1, s9, 8
    sb   t1, 37(t0)
    srli t1, s9, 16
    sb   t1, 38(t0)
    srli t1, s9, 24
    sb   t1, 39(t0)
    lw   t1, 608(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    sw   t1, 608(s0)
    sb   a0, 40(t0)
    srli t1, a0, 8
    sb   t1, 41(t0)
    srli t1, a0, 16
    sb   t1, 42(t0)
    srli t1, a0, 24
    sb   t1, 43(t0)
    sb   a1, 44(t0)
    srli t1, a1, 8
    sb   t1, 45(t0)
    srli t1, a1, 16
    sb   t1, 46(t0)
    srli t1, a1, 24
    sb   t1, 47(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   a2, 48(t0)
    srli t1, a2, 8
    sb   t1, 49(t0)
    srli t1, a2, 16
    sb   t1, 50(t0)
    srli t1, a2, 24
    sb   t1, 51(t0)
    sb   a3, 52(t0)
    srli t1, a3, 8
    sb   t1, 53(t0)
    srli t1, a3, 16
    sb   t1, 54(t0)
    srli t1, a3, 24
    sb   t1, 55(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   a4, 56(t0)
    srli t1, a4, 8
    sb   t1, 57(t0)
    srli t1, a4, 16
    sb   t1, 58(t0)
    srli t1, a4, 24
    sb   t1, 59(t0)
    sb   a5, 60(t0)
    srli t1, a5, 8
    sb   t1, 61(t0)
    srli t1, a5, 16
    sb   t1, 62(t0)
    srli t1, a5, 24
    sb   t1, 63(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   a6, 64(t0)
    srli t1, a6, 8
    sb   t1, 65(t0)
    srli t1, a6, 16
    sb   t1, 66(t0)
    srli t1, a6, 24
    sb   t1, 67(t0)
    sb   a7, 68(t0)
    srli t1, a7, 8
    sb   t1, 69(t0)
    srli t1, a7, 16
    sb   t1, 70(t0)
    srli t1, a7, 24
    sb   t1, 71(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   s6, 72(t0)
    srli t1, s6, 8
    sb   t1, 73(t0)
    srli t1, s6, 16
    sb   t1, 74(t0)
    srli t1, s6, 24
    sb   t1, 75(t0)
    sb   t6, 76(t0)
    srli t1, t6, 8
    sb   t1, 77(t0)
    srli t1, t6, 16
    sb   t1, 78(t0)
    srli t1, t6, 24
    sb   t1, 79(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   s6, 80(t0)
    srli t1, s6, 8
    sb   t1, 81(t0)
    srli t1, s6, 16
    sb   t1, 82(t0)
    srli t1, s6, 24
    sb   t1, 83(t0)
    sb   t6, 84(t0)
    srli t1, t6, 8
    sb   t1, 85(t0)
    srli t1, t6, 16
    sb   t1, 86(t0)
    srli t1, t6, 24
    sb   t1, 87(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   s6, 88(t0)
    srli t1, s6, 8
    sb   t1, 89(t0)
    srli t1, s6, 16
    sb   t1, 90(t0)
    srli t1, s6, 24
    sb   t1, 91(t0)
    sb   t6, 92(t0)
    srli t1, t6, 8
    sb   t1, 93(t0)
    srli t1, t6, 16
    sb   t1, 94(t0)
    srli t1, t6, 24
    sb   t1, 95(t0)
    lw   t1, 608(s0)
    sw   t1, 608(s0)
    sb   s6, 96(t0)
    srli t1, s6, 8
    sb   t1, 97(t0)
    srli t1, s6, 16
    sb   t1, 98(t0)
    srli t1, s6, 24
    sb   t1, 99(t0)
    sb   t6, 100(t0)
    srli t1, t6, 8
    sb   t1, 101(t0)
    srli t1, t6, 16
    sb   t1, 102(t0)
    srli t1, t6, 24
    sb   t1, 103(t0)
    lw   t1, 608(s0)
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_mul
.p2align 2
eita_handler_mul:
    li   s7, 64
    bnez zero, .Lx1094
    bltu s2, s7, eita_stack_underflow
.Lx1094:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_mul
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_div
.p2align 2
eita_handler_div:
    li   s7, 64
    bnez zero, .Lx1142
    bltu s2, s7, eita_stack_underflow
.Lx1142:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_div
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_sdiv
.p2align 2
eita_handler_sdiv:
    li   s7, 64
    bnez zero, .Lx1190
    bltu s2, s7, eita_stack_underflow
.Lx1190:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_sdiv
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_mod
.p2align 2
eita_handler_mod:
    li   s7, 64
    bnez zero, .Lx1238
    bltu s2, s7, eita_stack_underflow
.Lx1238:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_mod
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_smod
.p2align 2
eita_handler_smod:
    li   s7, 64
    bnez zero, .Lx1286
    bltu s2, s7, eita_stack_underflow
.Lx1286:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_smod
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_shl
.p2align 2
eita_handler_shl:
    li   s7, 64
    bnez zero, .Lx1334
    bltu s2, s7, eita_stack_underflow
.Lx1334:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_shl
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_shr
.p2align 2
eita_handler_shr:
    li   s7, 64
    bnez zero, .Lx1382
    bltu s2, s7, eita_stack_underflow
.Lx1382:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_shr
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_sar
.p2align 2
eita_handler_sar:
    li   s7, 64
    bnez zero, .Lx1430
    bltu s2, s7, eita_stack_underflow
.Lx1430:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_sar
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_byte
.p2align 2
eita_handler_byte:
    li   s7, 64
    bnez zero, .Lx1478
    bltu s2, s7, eita_stack_underflow
.Lx1478:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_byte
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_signextend
.p2align 2
eita_handler_signextend:
    li   s7, 64
    bnez zero, .Lx1526
    bltu s2, s7, eita_stack_underflow
.Lx1526:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_signextend
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_addmod
.p2align 2
eita_handler_addmod:
    li   s7, 96
    bnez zero, .Lx1574
    bltu s2, s7, eita_stack_underflow
.Lx1574:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, s2, -96
    add  a3, s3, a3
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_addmod
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 8
    addi s5, s5, -8
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_mulmod
.p2align 2
eita_handler_mulmod:
    li   s7, 96
    bnez zero, .Lx1626
    bltu s2, s7, eita_stack_underflow
.Lx1626:
    addi sp, sp, -32
    addi a0, sp, 0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, s2, -96
    add  a3, s3, a3
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_mulmod
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 8
    addi s5, s5, -8
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_calldataload
.p2align 2
eita_handler_calldataload:
    li   s7, 32
    bnez zero, .Lx1678
    bltu s2, s7, eita_stack_underflow
.Lx1678:
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    addi a0, sp, 0
    mv   a1, s0
    addi a2, s2, -32
    add  a2, s3, a2
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_calldataload
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_calldatacopy
.p2align 2
eita_handler_calldatacopy:
    li   s7, 96
    bnez zero, .Lx1726
    bltu s2, s7, eita_stack_underflow
.Lx1726:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t4, s3, t2
    sltu s7, t4, t2
    add  t5, zero, s7
    add  t5, t5, t3
    lw   t2, 0(t4)
    lw   t3, 4(t4)
    lw   s10, 8(t4)
    lw   s11, 12(t4)
    lw   t0, 16(t4)
    lw   t1, 20(t4)
    or   s10, s10, t0
    or   s11, s11, t1
    lw   t0, 24(t4)
    lw   t1, 28(t4)
    or   s10, s10, t0
    or   s11, s11, t1
    or   s7, s10, s11
    bnez s7, eita_oog
    li   s8, 3
    li   s9, 0
    addi s10, t2, 31
    sltiu s7, s10, 31
    add  s11, t3, s7
    bltu s11, t3, eita_oog
    bne  s11, t3, .Lx1737
    bltu s10, t2, eita_oog
.Lx1737:
    srli s10, s10, 5
    slli s7, s11, 27
    or   s10, s10, s7
    srli s11, s11, 5
    slli t6, s11, 1
    srli s7, s10, 31
    or   t6, t6, s7
    slli s6, s10, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    or   s7, t2, t3
    beqz s7, 6f
    or   s10, a2, a4
    or   s11, a3, a5
    or   s10, s10, a6
    or   s11, s11, a7
    or   s7, s10, s11
    bnez s7, eita_oog
    add  t0, a0, t2
    sltu s7, t0, t2
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t3
    bgeu t1, t3, .Lk3491
    addi s7, s7, 1
.Lk3491:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx1748
    bltu t2, t0, eita_oog
.Lx1748:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx1753
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx1753:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
6:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    mv   a0, s0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, s2, -96
    add  a3, s3, a3
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_calldatacopy
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltiu s7, s2, 96
    addi s2, s2, -96
    sub  zero, zero, s7
    li   s7, 32
    blt  zero, zero, 7f
    bnez zero, .Lx1779
    bltu s2, s7, 7f
.Lx1779:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
7:
    ret
.text
.globl eita_handler_codecopy
.p2align 2
eita_handler_codecopy:
    li   s7, 96
    bnez zero, .Lx1858
    bltu s2, s7, eita_stack_underflow
.Lx1858:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t4, s3, t2
    sltu s7, t4, t2
    add  t5, zero, s7
    add  t5, t5, t3
    lw   t2, 0(t4)
    lw   t3, 4(t4)
    lw   s10, 8(t4)
    lw   s11, 12(t4)
    lw   t0, 16(t4)
    lw   t1, 20(t4)
    or   s10, s10, t0
    or   s11, s11, t1
    lw   t0, 24(t4)
    lw   t1, 28(t4)
    or   s10, s10, t0
    or   s11, s11, t1
    or   s7, s10, s11
    bnez s7, eita_oog
    li   s8, 3
    li   s9, 0
    addi s10, t2, 31
    sltiu s7, s10, 31
    add  s11, t3, s7
    bltu s11, t3, eita_oog
    bne  s11, t3, .Lx1869
    bltu s10, t2, eita_oog
.Lx1869:
    srli s10, s10, 5
    slli s7, s11, 27
    or   s10, s10, s7
    srli s11, s11, 5
    slli t6, s11, 1
    srli s7, s10, 31
    or   t6, t6, s7
    slli s6, s10, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    or   s7, t2, t3
    beqz s7, 6f
    or   s10, a2, a4
    or   s11, a3, a5
    or   s10, s10, a6
    or   s11, s11, a7
    or   s7, s10, s11
    bnez s7, eita_oog
    add  t0, a0, t2
    sltu s7, t0, t2
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t3
    bgeu t1, t3, .Lk3755
    addi s7, s7, 1
.Lk3755:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx1880
    bltu t2, t0, eita_oog
.Lx1880:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx1885
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx1885:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
6:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    mv   a0, s0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, s2, -96
    add  a3, s3, a3
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_codecopy
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltiu s7, s2, 96
    addi s2, s2, -96
    sub  zero, zero, s7
    li   s7, 32
    blt  zero, zero, 7f
    bnez zero, .Lx1911
    bltu s2, s7, 7f
.Lx1911:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
7:
    ret
.text
.globl eita_handler_returndatacopy
.p2align 2
eita_handler_returndatacopy:
    li   s7, 96
    bnez zero, .Lx1990
    bltu s2, s7, eita_stack_underflow
.Lx1990:
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s10, 16(t2)
    lw   s11, 20(t2)
    or   t4, t4, s10
    or   t5, t5, s11
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    or   t4, t4, s10
    or   t5, t5, s11
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, t4, s6
    sltu s7, t4, s6
    add  t5, t5, s7
    sltu s7, t5, s7
    add  t5, t5, t6
    bgeu t5, t6, .Lk4007
    addi s7, s7, 1
.Lk4007:
    bnez s7, eita_oog
    lw   s10, 104(s0)
    lw   s11, 108(s0)
    bltu s11, t5, eita_oog
    bne  s11, t5, .Lx2006
    bltu s10, t4, eita_oog
.Lx2006:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t4, s3, t2
    sltu s7, t4, t2
    add  t5, zero, s7
    add  t5, t5, t3
    lw   t2, 0(t4)
    lw   t3, 4(t4)
    lw   s10, 8(t4)
    lw   s11, 12(t4)
    lw   t0, 16(t4)
    lw   t1, 20(t4)
    or   s10, s10, t0
    or   s11, s11, t1
    lw   t0, 24(t4)
    lw   t1, 28(t4)
    or   s10, s10, t0
    or   s11, s11, t1
    or   s7, s10, s11
    bnez s7, eita_oog
    li   s8, 3
    li   s9, 0
    addi s10, t2, 31
    sltiu s7, s10, 31
    add  s11, t3, s7
    bltu s11, t3, eita_oog
    bne  s11, t3, .Lx2017
    bltu s10, t2, eita_oog
.Lx2017:
    srli s10, s10, 5
    slli s7, s11, 27
    or   s10, s10, s7
    srli s11, s11, 5
    slli t6, s11, 1
    srli s7, s10, 31
    or   t6, t6, s7
    slli s6, s10, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    or   s7, t2, t3
    beqz s7, 6f
    or   s10, a2, a4
    or   s11, a3, a5
    or   s10, s10, a6
    or   s11, s11, a7
    or   s7, s10, s11
    bnez s7, eita_oog
    add  t0, a0, t2
    sltu s7, t0, t2
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t3
    bgeu t1, t3, .Lk4051
    addi s7, s7, 1
.Lk4051:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx2028
    bltu t2, t0, eita_oog
.Lx2028:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx2033
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx2033:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
6:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    mv   a0, s0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, s2, -96
    add  a3, s3, a3
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_returndatacopy
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltiu s7, s2, 96
    addi s2, s2, -96
    sub  zero, zero, s7
    li   s7, 32
    blt  zero, zero, 7f
    bnez zero, .Lx2059
    bltu s2, s7, 7f
.Lx2059:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
7:
    ret
.text
.globl eita_handler_mcopy
.p2align 2
eita_handler_mcopy:
    li   s7, 96
    bnez zero, .Lx2156
    bltu s2, s7, eita_stack_underflow
.Lx2156:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lmcd0
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk4353
    addi s7, s7, 1
.Lk4353:
    bnez s7, eita_oog
    j    .Lmcd1
.Lmcd0:
    li   t0, 0
    li   t1, 0
.Lmcd1:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lmcs0
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t2, s8, s10
    sltu s7, t2, s10
    add  t3, s9, s7
    sltu s7, t3, s7
    add  t3, t3, s11
    bgeu t3, s11, .Lk4403
    addi s7, s7, 1
.Lk4403:
    bnez s7, eita_oog
    j    .Lmcs1
.Lmcs0:
    li   t2, 0
    li   t3, 0
.Lmcs1:
    bltu t3, t1, .Lm2207
    bne  t3, t1, .Lx2207
    bltu t2, t0, .Lm2207
.Lx2207:
    mv   t0, t2
    mv   t1, t3
    j    .Ln2207
.Lm2207:
    mv   t0, t0
    mv   t1, t1
.Ln2207:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t4, s3, t2
    sltu s7, t4, t2
    add  t5, zero, s7
    add  t5, t5, t3
    lw   t2, 0(t4)
    lw   t3, 4(t4)
    li   s8, 3
    li   s9, 0
    addi s10, t2, 31
    sltiu s7, s10, 31
    add  s11, t3, s7
    bltu s11, t3, eita_oog
    bne  s11, t3, .Lx2213
    bltu s10, t2, eita_oog
.Lx2213:
    srli s10, s10, 5
    slli s7, s11, 27
    or   s10, s10, s7
    srli s11, s11, 5
    slli t6, s11, 1
    srli s7, s10, 31
    or   t6, t6, s7
    slli s6, s10, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    or   s7, t0, t1
    beqz s7, 6f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx2219
    bltu t2, t0, eita_oog
.Lx2219:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx2224
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx2224:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
6:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    mv   a0, s0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, s2, -96
    add  a3, s3, a3
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_mcopy
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltiu s7, s2, 96
    addi s2, s2, -96
    sub  zero, zero, s7
    li   s7, 32
    blt  zero, zero, 7f
    bnez zero, .Lx2250
    bltu s2, s7, 7f
.Lx2250:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
7:
    ret
.text
.globl eita_handler_keccak256
.p2align 2
eita_handler_keccak256:
    li   s7, 64
    bnez zero, .Lx2372
    bltu s2, s7, eita_stack_underflow
.Lx2372:
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    addi s8, s6, 31
    sltiu s7, s8, 31
    add  s9, t6, s7
    bltu s9, t6, eita_oog
    bne  s9, t6, .Lx2377
    bltu s8, s6, eita_oog
.Lx2377:
    srli s8, s8, 5
    slli s7, s9, 27
    or   s8, s8, s7
    srli s9, s9, 5
    slli t6, s9, 1
    srli s7, s8, 31
    or   t6, t6, s7
    slli s6, s8, 1
    add  s8, s8, s6
    sltu s7, s8, s6
    add  s9, s9, t6
    add  s9, s9, s7
    srli s7, s8, 31
    add  s8, s8, s8
    add  s9, s9, s9
    add  s9, s9, s7
    addi s8, s8, 30
    sltiu s7, s8, 30
    add  s9, s9, s7
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   s7, s6, t6
    beqz s7, 4f
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t0, a0, s6
    sltu s7, t0, s6
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t6
    bgeu t1, t6, .Lk4773
    addi s7, s7, 1
.Lk4773:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx2389
    bltu t2, t0, eita_oog
.Lx2389:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx2394
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx2394:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
4:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi sp, sp, -32
    mv   a0, s0
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, s2, -64
    add  a2, s3, a2
    addi a3, sp, 0
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_keccak256
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_sload
.p2align 2
eita_handler_sload:
    li   s7, 32
    bnez zero, .Lx2500
    bltu s2, s7, eita_stack_underflow
.Lx2500:
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    addi a1, s0, 144
    addi a2, s2, -32
    add  a2, s3, a2
    addi a3, sp, 0
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 4(t0)
    lw   t0, 0(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_tload
.p2align 2
eita_handler_tload:
    li   s7, 32
    bnez zero, .Lx2554
    bltu s2, s7, eita_stack_underflow
.Lx2554:
    li   t2, 100
    li   t3, 0
    sltu s7, s5, t2
    sub  s5, s5, t2
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t3
    sub  zero, zero, t3
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    lw   a0, 64(a0)
    addi a1, s0, 144
    addi a2, s2, -32
    add  a2, s3, a2
    addi a3, sp, 0
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_ts_tload
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_balance
.p2align 2
eita_handler_balance:
    li   s7, 32
    bnez zero, .Lx2608
    bltu s2, s7, eita_stack_underflow
.Lx2608:
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, sp, 0
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 36(t0)
    lw   t0, 32(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_selfbalance
.p2align 2
eita_handler_selfbalance:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    addi a1, s0, 144
    addi a2, sp, 0
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 36(t0)
    lw   t0, 32(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 5
    addi s5, s5, -5
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_extcodesize
.p2align 2
eita_handler_extcodesize:
    li   s7, 32
    bnez zero, .Lx2712
    bltu s2, s7, eita_stack_underflow
.Lx2712:
    addi sp, sp, -16
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, sp, 0
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 44(t0)
    lw   t0, 40(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    mv   t2, t0
    mv   t3, t1
    sltu s7, s5, t2
    sub  s5, s5, t2
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t3
    sub  zero, zero, t3
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   a0, 0(sp)
    lw   a1, 4(sp)
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 16
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_extcodehash
.p2align 2
eita_handler_extcodehash:
    li   s7, 32
    bnez zero, .Lx2768
    bltu s2, s7, eita_stack_underflow
.Lx2768:
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, sp, 0
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 52(t0)
    lw   t0, 48(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_blockhash
.p2align 2
eita_handler_blockhash:
    li   s7, 32
    bnez zero, .Lx2820
    bltu s2, s7, eita_stack_underflow
.Lx2820:
    addi sp, sp, -32
    addi sp, sp, -16
    sw   ra, 8(sp)
    lw   a0, 504(s0)
    addi a1, s2, -32
    add  a1, s3, a1
    addi a2, sp, 0
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 68(t0)
    lw   t0, 64(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    addi t2, sp, 0
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    lw   ra, 8(sp)
    addi sp, sp, 16
    addi sp, sp, 32
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 20
    addi s5, s5, -20
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_extcodecopy
.p2align 2
eita_handler_extcodecopy:
    li   s7, 128
    bnez zero, .Lx2872
    bltu s2, s7, eita_stack_underflow
.Lx2872:
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lxcd0
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk5785
    addi s7, s7, 1
.Lk5785:
    bnez s7, eita_oog
    j    .Lxcd1
.Lxcd0:
    li   t0, 0
    li   t1, 0
.Lxcd1:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 90f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx2901
    bltu t2, t0, eita_oog
.Lx2901:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx2906
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx2906:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
90:
    lw   s10, 504(s0)
    lw   s11, 508(s0)
    sltiu s7, s2, 32
    addi s8, s2, -32
    sub  s9, zero, s7
    add  s8, s8, s3
    sltu s7, s8, s3
    add  s9, s9, s7
    add  s9, s9, zero
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a6, 0(t2)
    lw   a7, 4(t2)
    lw   a4, 40(s0)
    lw   a5, 44(s0)
    add  t4, a4, a6
    sltu s7, t4, a6
    add  t5, a5, s7
    add  t5, t5, a7
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a6, 8(t2)
    lw   a7, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    or   a6, a6, a4
    or   a7, a7, a5
    lw   a4, 24(t2)
    lw   a5, 28(t2)
    or   a6, a6, a4
    or   a7, a7, a5
    lw   t3, 4(t2)
    lw   t2, 0(t2)
    or   s7, a6, a7
    beqz s7, 94f
    li   t2, 0
    li   t3, 0
    sltiu s7, t2, 1
    addi t2, t2, -1
    sub  t3, t3, s7
94:
    sltiu s7, s2, 128
    addi a0, s2, -128
    sub  a1, zero, s7
    add  a0, a0, s3
    sltu s7, a0, s3
    add  a1, a1, s7
    add  a1, a1, zero
    lw   a1, 4(a0)
    lw   a0, 0(a0)
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    mv   t3, t0
    lbu  t0, 56(t3)
    lbu  t2, 57(t3)
    slli t2, t2, 8
    or   t0, t0, t2
    lbu  t2, 58(t3)
    slli t2, t2, 16
    or   t0, t0, t2
    lbu  t2, 59(t3)
    slli t2, t2, 24
    or   t0, t0, t2
    lbu  t1, 60(t3)
    lbu  t2, 61(t3)
    slli t2, t2, 8
    or   t1, t1, t2
    lbu  t2, 62(t3)
    slli t2, t2, 16
    or   t1, t1, t2
    lbu  t2, 63(t3)
    slli t2, t2, 24
    or   t1, t1, t2
    lw   t3, 612(s0)
    lw   t2, 608(s0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    sltiu s7, s2, 128
    addi s2, s2, -128
    sub  zero, zero, s7
    li   s7, 32
    blt  zero, zero, 91f
    bnez zero, .Lx2952
    bltu s2, s7, 91f
.Lx2952:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
91:
    ret
.text
.globl eita_handler_staticcall
.p2align 2
eita_handler_staticcall:
    li   s7, 192
    bnez zero, .Lx3056
    bltu s2, s7, eita_stack_underflow
.Lx3056:
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfin0_staticcall
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk6153
    addi s7, s7, 1
.Lk6153:
    bnez s7, eita_oog
    j    .Lcfin1_staticcall
.Lcfin0_staticcall:
    li   t0, 0
    li   t1, 0
.Lcfin1_staticcall:
    sltiu s7, s2, 192
    addi t2, s2, -192
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfout0_staticcall
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t2, s8, s10
    sltu s7, t2, s10
    add  t3, s9, s7
    sltu s7, t3, s7
    add  t3, t3, s11
    bgeu t3, s11, .Lk6203
    addi s7, s7, 1
.Lk6203:
    bnez s7, eita_oog
    j    .Lcfout1_staticcall
.Lcfout0_staticcall:
    li   t2, 0
    li   t3, 0
.Lcfout1_staticcall:
    bltu t3, t1, .Lm3107
    bne  t3, t1, .Lx3107
    bltu t2, t0, .Lm3107
.Lx3107:
    mv   t0, t2
    mv   t1, t3
    j    .Ln3107
.Lm3107:
    mv   t0, t0
    mv   t1, t1
.Ln3107:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx3111
    bltu t2, t0, eita_oog
.Lx3111:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx3116
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx3116:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    addi sp, sp, -192
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    mv   t2, s2
    mv   t3, zero
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    sw   t2, 16(s0)
    sw   t3, 20(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    li   t0, 3
    li   t1, 0
    sw   t0, 0(sp)
    li   t0, 1
    li   t1, 0
    sw   t0, 4(sp)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 8(sp)
    sw   t1, 12(sp)
    sw   t4, 16(sp)
    sw   t5, 20(sp)
    sw   s8, 24(sp)
    sw   s9, 28(sp)
    sw   s10, 32(sp)
    sw   s11, 36(sp)
    sw   zero, 40(sp)
    sw   zero, 44(sp)
    sw   zero, 48(sp)
    sw   zero, 52(sp)
    sw   zero, 56(sp)
    sw   zero, 60(sp)
    sw   zero, 64(sp)
    sw   zero, 68(sp)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 40(s0)
    lw   s11, 44(s0)
    add  t4, t4, s10
    sltu s7, t4, s10
    add  t5, t5, s7
    add  t5, t5, s11
    sw   t4, 72(sp)
    sw   t5, 76(sp)
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    sw   t4, 80(sp)
    sw   t5, 84(sp)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 8(t2)
    lw   s11, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    or   s10, s10, a4
    or   s11, s11, a5
    or   s10, s10, a6
    or   s11, s11, a7
    li   s7, 0
    bnez s11, .Lne3171
    bne  s10, s7, .Lne3171
    mv   t4, t4
    mv   t5, t5
    j    .Lsd3171
.Lne3171:
    li   t4, -1
    li   t5, -1
.Lsd3171:
    sw   t4, 88(sp)
    sw   t5, 92(sp)
    sw   zero, 96(sp)
    sw   zero, 100(sp)
    sw   zero, 104(sp)
    sw   zero, 108(sp)
    sw   zero, 112(sp)
    sw   zero, 116(sp)
    sw   zero, 120(sp)
    sw   zero, 124(sp)
    lw   a0, 504(s0)
    addi a1, sp, 0
    addi a2, sp, 128
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 92(t0)
    lw   t0, 88(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t0, 136(sp)
    lw   t1, 140(sp)
    sw   t0, 96(s0)
    sw   t1, 100(s0)
    lw   t0, 144(sp)
    lw   t1, 148(sp)
    sw   t0, 104(s0)
    sw   t1, 108(s0)
    addi a3, s2, -160
    add  a3, s3, a3
    lw   a1, 0(a3)
    addi a3, s2, -192
    add  a3, s3, a3
    lw   a2, 0(a3)
    mv   a0, s0
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_returndata_to_mem
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t4, 128(sp)
    li   t5, 0
    lw   t0, 152(sp)
    lw   t1, 156(sp)
    sltiu s7, s2, 160
    addi s2, s2, -160
    sub  zero, zero, s7
    mv   a0, t4
    mv   a1, t5
    li   s7, 255
    and  a0, a0, s7
    li   s7, 0
    and  a1, a1, s7
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   s5, 8(s0)
    lw   zero, 12(s0)
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi sp, sp, 192
    ret
.text
.globl eita_handler_call
.p2align 2
eita_handler_call:
    li   s7, 224
    bnez zero, .Lx3376
    bltu s2, s7, eita_stack_underflow
.Lx3376:
    lbu  t2, 130(s0)
    li   t3, 0
    beqz t2, 93f
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 8(t2)
    lw   s11, 12(t2)
    or   t4, t4, s10
    or   t5, t5, s11
    lw   s10, 16(t2)
    lw   s11, 20(t2)
    or   t4, t4, s10
    or   t5, t5, s11
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    or   t4, t4, s10
    or   t5, t5, s11
    or   s7, t4, t5
    bnez s7, eita_static_violation
93:
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfin0_call
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk6819
    addi s7, s7, 1
.Lk6819:
    bnez s7, eita_oog
    j    .Lcfin1_call
.Lcfin0_call:
    li   t0, 0
    li   t1, 0
.Lcfin1_call:
    sltiu s7, s2, 224
    addi t2, s2, -224
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 192
    addi t2, s2, -192
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfout0_call
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t2, s8, s10
    sltu s7, t2, s10
    add  t3, s9, s7
    sltu s7, t3, s7
    add  t3, t3, s11
    bgeu t3, s11, .Lk6869
    addi s7, s7, 1
.Lk6869:
    bnez s7, eita_oog
    j    .Lcfout1_call
.Lcfout0_call:
    li   t2, 0
    li   t3, 0
.Lcfout1_call:
    bltu t3, t1, .Lm3440
    bne  t3, t1, .Lx3440
    bltu t2, t0, .Lm3440
.Lx3440:
    mv   t0, t2
    mv   t1, t3
    j    .Ln3440
.Lm3440:
    mv   t0, t0
    mv   t1, t1
.Ln3440:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx3444
    bltu t2, t0, eita_oog
.Lx3444:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx3449
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx3449:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    addi sp, sp, -192
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    mv   t2, s2
    mv   t3, zero
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    sw   t2, 16(s0)
    sw   t3, 20(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    li   t0, 0
    li   t1, 0
    sw   t0, 0(sp)
    li   t0, 0
    li   t1, 0
    sw   t0, 4(sp)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 8(sp)
    sw   t1, 12(sp)
    sw   t4, 16(sp)
    sw   t5, 20(sp)
    sw   s8, 24(sp)
    sw   s9, 28(sp)
    sw   s10, 32(sp)
    sw   s11, 36(sp)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 40(sp)
    sw   t1, 44(sp)
    sw   t4, 48(sp)
    sw   t5, 52(sp)
    sw   s8, 56(sp)
    sw   s9, 60(sp)
    sw   s10, 64(sp)
    sw   s11, 68(sp)
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 40(s0)
    lw   s11, 44(s0)
    add  t4, t4, s10
    sltu s7, t4, s10
    add  t5, t5, s7
    add  t5, t5, s11
    sw   t4, 72(sp)
    sw   t5, 76(sp)
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    sw   t4, 80(sp)
    sw   t5, 84(sp)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 8(t2)
    lw   s11, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    or   s10, s10, a4
    or   s11, s11, a5
    or   s10, s10, a6
    or   s11, s11, a7
    li   s7, 0
    bnez s11, .Lne3508
    bne  s10, s7, .Lne3508
    mv   t4, t4
    mv   t5, t5
    j    .Lsd3508
.Lne3508:
    li   t4, -1
    li   t5, -1
.Lsd3508:
    sw   t4, 88(sp)
    sw   t5, 92(sp)
    sw   zero, 96(sp)
    sw   zero, 100(sp)
    sw   zero, 104(sp)
    sw   zero, 108(sp)
    sw   zero, 112(sp)
    sw   zero, 116(sp)
    sw   zero, 120(sp)
    sw   zero, 124(sp)
    lw   a0, 504(s0)
    addi a1, sp, 0
    addi a2, sp, 128
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 92(t0)
    lw   t0, 88(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t0, 136(sp)
    lw   t1, 140(sp)
    sw   t0, 96(s0)
    sw   t1, 100(s0)
    lw   t0, 144(sp)
    lw   t1, 148(sp)
    sw   t0, 104(s0)
    sw   t1, 108(s0)
    addi a3, s2, -192
    add  a3, s3, a3
    lw   a1, 0(a3)
    addi a3, s2, -224
    add  a3, s3, a3
    lw   a2, 0(a3)
    mv   a0, s0
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_returndata_to_mem
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t4, 128(sp)
    li   t5, 0
    lw   t0, 152(sp)
    lw   t1, 156(sp)
    sltiu s7, s2, 192
    addi s2, s2, -192
    sub  zero, zero, s7
    mv   a0, t4
    mv   a1, t5
    li   s7, 255
    and  a0, a0, s7
    li   s7, 0
    and  a1, a1, s7
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   s5, 8(s0)
    lw   zero, 12(s0)
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi sp, sp, 192
    ret
.text
.globl eita_handler_callcode
.p2align 2
eita_handler_callcode:
    li   s7, 224
    bnez zero, .Lx3730
    bltu s2, s7, eita_stack_underflow
.Lx3730:
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfin0_callcode
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk7501
    addi s7, s7, 1
.Lk7501:
    bnez s7, eita_oog
    j    .Lcfin1_callcode
.Lcfin0_callcode:
    li   t0, 0
    li   t1, 0
.Lcfin1_callcode:
    sltiu s7, s2, 224
    addi t2, s2, -224
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 192
    addi t2, s2, -192
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfout0_callcode
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t2, s8, s10
    sltu s7, t2, s10
    add  t3, s9, s7
    sltu s7, t3, s7
    add  t3, t3, s11
    bgeu t3, s11, .Lk7551
    addi s7, s7, 1
.Lk7551:
    bnez s7, eita_oog
    j    .Lcfout1_callcode
.Lcfout0_callcode:
    li   t2, 0
    li   t3, 0
.Lcfout1_callcode:
    bltu t3, t1, .Lm3781
    bne  t3, t1, .Lx3781
    bltu t2, t0, .Lm3781
.Lx3781:
    mv   t0, t2
    mv   t1, t3
    j    .Ln3781
.Lm3781:
    mv   t0, t0
    mv   t1, t1
.Ln3781:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx3785
    bltu t2, t0, eita_oog
.Lx3785:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx3790
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx3790:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    addi sp, sp, -192
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    mv   t2, s2
    mv   t3, zero
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    sw   t2, 16(s0)
    sw   t3, 20(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    li   t0, 1
    li   t1, 0
    sw   t0, 0(sp)
    li   t0, 0
    li   t1, 0
    sw   t0, 4(sp)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 8(sp)
    sw   t1, 12(sp)
    sw   t4, 16(sp)
    sw   t5, 20(sp)
    sw   s8, 24(sp)
    sw   s9, 28(sp)
    sw   s10, 32(sp)
    sw   s11, 36(sp)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 40(sp)
    sw   t1, 44(sp)
    sw   t4, 48(sp)
    sw   t5, 52(sp)
    sw   s8, 56(sp)
    sw   s9, 60(sp)
    sw   s10, 64(sp)
    sw   s11, 68(sp)
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 40(s0)
    lw   s11, 44(s0)
    add  t4, t4, s10
    sltu s7, t4, s10
    add  t5, t5, s7
    add  t5, t5, s11
    sw   t4, 72(sp)
    sw   t5, 76(sp)
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    sw   t4, 80(sp)
    sw   t5, 84(sp)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 8(t2)
    lw   s11, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    or   s10, s10, a4
    or   s11, s11, a5
    or   s10, s10, a6
    or   s11, s11, a7
    li   s7, 0
    bnez s11, .Lne3849
    bne  s10, s7, .Lne3849
    mv   t4, t4
    mv   t5, t5
    j    .Lsd3849
.Lne3849:
    li   t4, -1
    li   t5, -1
.Lsd3849:
    sw   t4, 88(sp)
    sw   t5, 92(sp)
    sw   zero, 96(sp)
    sw   zero, 100(sp)
    sw   zero, 104(sp)
    sw   zero, 108(sp)
    sw   zero, 112(sp)
    sw   zero, 116(sp)
    sw   zero, 120(sp)
    sw   zero, 124(sp)
    lw   a0, 504(s0)
    addi a1, sp, 0
    addi a2, sp, 128
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 92(t0)
    lw   t0, 88(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t0, 136(sp)
    lw   t1, 140(sp)
    sw   t0, 96(s0)
    sw   t1, 100(s0)
    lw   t0, 144(sp)
    lw   t1, 148(sp)
    sw   t0, 104(s0)
    sw   t1, 108(s0)
    addi a3, s2, -192
    add  a3, s3, a3
    lw   a1, 0(a3)
    addi a3, s2, -224
    add  a3, s3, a3
    lw   a2, 0(a3)
    mv   a0, s0
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_returndata_to_mem
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t4, 128(sp)
    li   t5, 0
    lw   t0, 152(sp)
    lw   t1, 156(sp)
    sltiu s7, s2, 192
    addi s2, s2, -192
    sub  zero, zero, s7
    mv   a0, t4
    mv   a1, t5
    li   s7, 255
    and  a0, a0, s7
    li   s7, 0
    and  a1, a1, s7
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   s5, 8(s0)
    lw   zero, 12(s0)
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi sp, sp, 192
    ret
.text
.globl eita_handler_delegatecall
.p2align 2
eita_handler_delegatecall:
    li   s7, 192
    bnez zero, .Lx4058
    bltu s2, s7, eita_stack_underflow
.Lx4058:
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfin0_delegatecall
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk8157
    addi s7, s7, 1
.Lk8157:
    bnez s7, eita_oog
    j    .Lcfin1_delegatecall
.Lcfin0_delegatecall:
    li   t0, 0
    li   t1, 0
.Lcfin1_delegatecall:
    sltiu s7, s2, 192
    addi t2, s2, -192
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcfout0_delegatecall
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t2, s8, s10
    sltu s7, t2, s10
    add  t3, s9, s7
    sltu s7, t3, s7
    add  t3, t3, s11
    bgeu t3, s11, .Lk8207
    addi s7, s7, 1
.Lk8207:
    bnez s7, eita_oog
    j    .Lcfout1_delegatecall
.Lcfout0_delegatecall:
    li   t2, 0
    li   t3, 0
.Lcfout1_delegatecall:
    bltu t3, t1, .Lm4109
    bne  t3, t1, .Lx4109
    bltu t2, t0, .Lm4109
.Lx4109:
    mv   t0, t2
    mv   t1, t3
    j    .Ln4109
.Lm4109:
    mv   t0, t0
    mv   t1, t1
.Ln4109:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx4113
    bltu t2, t0, eita_oog
.Lx4113:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx4118
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx4118:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    addi sp, sp, -192
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    mv   t2, s2
    mv   t3, zero
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    sw   t2, 16(s0)
    sw   t3, 20(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    li   t0, 2
    li   t1, 0
    sw   t0, 0(sp)
    li   t0, 0
    li   t1, 0
    sw   t0, 4(sp)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 8(sp)
    sw   t1, 12(sp)
    sw   t4, 16(sp)
    sw   t5, 20(sp)
    sw   s8, 24(sp)
    sw   s9, 28(sp)
    sw   s10, 32(sp)
    sw   s11, 36(sp)
    sw   zero, 40(sp)
    sw   zero, 44(sp)
    sw   zero, 48(sp)
    sw   zero, 52(sp)
    sw   zero, 56(sp)
    sw   zero, 60(sp)
    sw   zero, 64(sp)
    sw   zero, 68(sp)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 40(s0)
    lw   s11, 44(s0)
    add  t4, t4, s10
    sltu s7, t4, s10
    add  t5, t5, s7
    add  t5, t5, s11
    sw   t4, 72(sp)
    sw   t5, 76(sp)
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    sw   t4, 80(sp)
    sw   t5, 84(sp)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 8(t2)
    lw   s11, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    or   s10, s10, a4
    or   s11, s11, a5
    or   s10, s10, a6
    or   s11, s11, a7
    li   s7, 0
    bnez s11, .Lne4173
    bne  s10, s7, .Lne4173
    mv   t4, t4
    mv   t5, t5
    j    .Lsd4173
.Lne4173:
    li   t4, -1
    li   t5, -1
.Lsd4173:
    sw   t4, 88(sp)
    sw   t5, 92(sp)
    sw   zero, 96(sp)
    sw   zero, 100(sp)
    sw   zero, 104(sp)
    sw   zero, 108(sp)
    sw   zero, 112(sp)
    sw   zero, 116(sp)
    sw   zero, 120(sp)
    sw   zero, 124(sp)
    lw   a0, 504(s0)
    addi a1, sp, 0
    addi a2, sp, 128
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 92(t0)
    lw   t0, 88(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t0, 136(sp)
    lw   t1, 140(sp)
    sw   t0, 96(s0)
    sw   t1, 100(s0)
    lw   t0, 144(sp)
    lw   t1, 148(sp)
    sw   t0, 104(s0)
    sw   t1, 108(s0)
    addi a3, s2, -160
    add  a3, s3, a3
    lw   a1, 0(a3)
    addi a3, s2, -192
    add  a3, s3, a3
    lw   a2, 0(a3)
    mv   a0, s0
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_helper_returndata_to_mem
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t4, 128(sp)
    li   t5, 0
    lw   t0, 152(sp)
    lw   t1, 156(sp)
    sltiu s7, s2, 160
    addi s2, s2, -160
    sub  zero, zero, s7
    mv   a0, t4
    mv   a1, t5
    li   s7, 255
    and  a0, a0, s7
    li   s7, 0
    and  a1, a1, s7
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   s5, 8(s0)
    lw   zero, 12(s0)
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi sp, sp, 192
    ret
.text
.globl eita_handler_create
.p2align 2
eita_handler_create:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 96
    bnez zero, .Lx4380
    bltu s2, s7, eita_stack_underflow
.Lx4380:
    addi sp, sp, -192
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    mv   t2, s2
    mv   t3, zero
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    sw   t2, 16(s0)
    sw   t3, 20(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcrin0_create
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk8821
    addi s7, s7, 1
.Lk8821:
    bnez s7, eita_oog
    j    .Lcrin1_create
.Lcrin0_create:
    li   t0, 0
    li   t1, 0
.Lcrin1_create:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx4419
    bltu t2, t0, eita_oog
.Lx4419:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx4424
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx4424:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    li   t0, 4
    li   t1, 0
    sw   t0, 0(sp)
    sw   zero, 4(sp)
    sw   zero, 8(sp)
    sw   zero, 12(sp)
    sw   zero, 16(sp)
    sw   zero, 20(sp)
    sw   zero, 24(sp)
    sw   zero, 28(sp)
    sw   zero, 32(sp)
    sw   zero, 36(sp)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 40(sp)
    sw   t1, 44(sp)
    sw   t4, 48(sp)
    sw   t5, 52(sp)
    sw   s8, 56(sp)
    sw   s9, 60(sp)
    sw   s10, 64(sp)
    sw   s11, 68(sp)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 40(s0)
    lw   s11, 44(s0)
    add  t4, t4, s10
    sltu s7, t4, s10
    add  t5, t5, s7
    add  t5, t5, s11
    sw   t4, 72(sp)
    sw   t5, 76(sp)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    sw   t4, 80(sp)
    sw   t5, 84(sp)
    sw   s5, 88(sp)
    sw   zero, 92(sp)
    sw   zero, 96(sp)
    sw   zero, 100(sp)
    sw   zero, 104(sp)
    sw   zero, 108(sp)
    sw   zero, 112(sp)
    sw   zero, 116(sp)
    sw   zero, 120(sp)
    sw   zero, 124(sp)
    lw   a0, 504(s0)
    addi a1, sp, 0
    addi a2, sp, 128
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 100(t0)
    lw   t0, 96(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t2, 136(sp)
    lw   t3, 140(sp)
    sw   t2, 96(s0)
    sw   t3, 100(s0)
    lw   t2, 144(sp)
    lw   t3, 148(sp)
    sw   t2, 104(s0)
    sw   t3, 108(s0)
    lw   t4, 128(sp)
    li   t5, 0
    beqz t4, L_create_fail
    addi t2, sp, 160
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    j    L_create_done
L_create_fail:
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
L_create_done:
    lw   t0, 152(sp)
    lw   t1, 156(sp)
    lw   s5, 8(s0)
    lw   zero, 12(s0)
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    addi sp, sp, 192
    ret
.text
.globl eita_handler_create2
.p2align 2
eita_handler_create2:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 128
    bnez zero, .Lx4630
    bltu s2, s7, eita_stack_underflow
.Lx4630:
    addi sp, sp, -192
    sw   s1, 0(s0)
    sw   zero, 4(s0)
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    mv   t2, s2
    mv   t3, zero
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    sw   t2, 16(s0)
    sw   t3, 20(s0)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lcrin0_create2
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk9321
    addi s7, s7, 1
.Lk9321:
    bnez s7, eita_oog
    j    .Lcrin1_create2
.Lcrin0_create2:
    li   t0, 0
    li   t1, 0
.Lcrin1_create2:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx4669
    bltu t2, t0, eita_oog
.Lx4669:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx4674
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx4674:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    sw   s5, 8(s0)
    sw   zero, 12(s0)
    li   t0, 5
    li   t1, 0
    sw   t0, 0(sp)
    sw   zero, 4(sp)
    sw   zero, 8(sp)
    sw   zero, 12(sp)
    sw   zero, 16(sp)
    sw   zero, 20(sp)
    sw   zero, 24(sp)
    sw   zero, 28(sp)
    sw   zero, 32(sp)
    sw   zero, 36(sp)
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 40(sp)
    sw   t1, 44(sp)
    sw   t4, 48(sp)
    sw   t5, 52(sp)
    sw   s8, 56(sp)
    sw   s9, 60(sp)
    sw   s10, 64(sp)
    sw   s11, 68(sp)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    lw   s10, 40(s0)
    lw   s11, 44(s0)
    add  t4, t4, s10
    sltu s7, t4, s10
    add  t5, t5, s7
    add  t5, t5, s11
    sw   t4, 72(sp)
    sw   t5, 76(sp)
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t4, 0(t2)
    lw   t5, 4(t2)
    sw   t4, 80(sp)
    sw   t5, 84(sp)
    sw   s5, 88(sp)
    sw   zero, 92(sp)
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   t0, 96(sp)
    sw   t1, 100(sp)
    sw   t4, 104(sp)
    sw   t5, 108(sp)
    sw   s8, 112(sp)
    sw   s9, 116(sp)
    sw   s10, 120(sp)
    sw   s11, 124(sp)
    lw   a0, 504(s0)
    addi a1, sp, 0
    addi a2, sp, 128
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 100(t0)
    lw   t0, 96(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    lw   t2, 136(sp)
    lw   t3, 140(sp)
    sw   t2, 96(s0)
    sw   t3, 100(s0)
    lw   t2, 144(sp)
    lw   t3, 148(sp)
    sw   t2, 104(s0)
    sw   t3, 108(s0)
    lw   t4, 128(sp)
    li   t5, 0
    beqz t4, L_create2_fail
    addi t2, sp, 160
    li   t3, 0
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    j    L_create2_done
L_create2_fail:
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
L_create2_done:
    lw   t0, 152(sp)
    lw   t1, 156(sp)
    lw   s5, 8(s0)
    lw   zero, 12(s0)
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    sltiu s7, s2, 96
    addi s2, s2, -96
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    addi sp, sp, 192
    ret
.text
.globl eita_handler_selfdestruct
.p2align 2
eita_handler_selfdestruct:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 32
    bnez zero, .Lx4888
    bltu s2, s7, eita_stack_underflow
.Lx4888:
    sltiu s7, s1, 1
    addi s1, s1, -1
    sub  zero, zero, s7
    li   t2, 5000
    li   t3, 0
    sltu s7, s5, t2
    sub  s5, s5, t2
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t3
    sub  zero, zero, t3
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   a0, 504(s0)
    addi a1, s0, 144
    mv   a2, a3
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    lw   t1, 108(t0)
    lw   t0, 104(t0)
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltu s7, s5, t0
    sub  s5, s5, t0
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    li   t2, 1
    li   t3, 0
    sb   t2, 128(s0)
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    j    eita_sync_and_ret
.text
.globl eita_handler_mload
.p2align 2
eita_handler_mload:
    li   s7, 32
    bnez zero, .Lx4936
    bltu s2, s7, eita_stack_underflow
.Lx4936:
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    addi t0, a0, 32
    sltiu s7, t0, 32
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, zero
    bgeu t1, zero, .Lk9881
    addi s7, s7, 1
.Lk9881:
    bnez s7, eita_oog
    li   s8, 3
    li   s9, 0
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx4944
    bltu t2, t0, eita_oog
.Lx4944:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx4949
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx4949:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t2, 40(s0)
    lw   t3, 44(s0)
    addi t4, a0, 32
    sltiu s7, t4, 32
    add  t5, a1, s7
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm4968
    bne  s11, t5, .Lx4968
    bltu s10, t4, .Lm4968
.Lx4968:
    mv   s10, s10
    mv   s11, s11
    j    .Ln4968
.Lm4968:
    mv   s10, t4
    mv   s11, t5
.Ln4968:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    add  t2, t2, a0
    sltu s7, t2, a0
    add  t3, t3, s7
    add  t3, t3, a1
    sw   t0, 608(s0)
    lbu  a0, 0(t2)
    lbu  t0, 1(t2)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t2)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t2)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t2)
    lbu  t0, 5(t2)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t2)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t2)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  a4, 16(t2)
    lbu  t0, 17(t2)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 18(t2)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 19(t2)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 20(t2)
    lbu  t0, 21(t2)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 22(t2)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 23(t2)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    lbu  a6, 24(t2)
    lbu  t0, 25(t2)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 26(t2)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 27(t2)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 28(t2)
    lbu  t0, 29(t2)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 30(t2)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 31(t2)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    mv   t2, a0
    mv   t3, a1
    mv   a0, a6
    mv   a1, a7
    mv   a6, t2
    mv   a7, t3
    mv   t2, a2
    mv   t3, a3
    mv   a2, a4
    mv   a3, a5
    mv   a4, t2
    mv   a5, t3
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    ret
.text
.globl eita_handler_mstore
.p2align 2
eita_handler_mstore:
    li   s7, 64
    bnez zero, .Lx5054
    bltu s2, s7, eita_stack_underflow
.Lx5054:
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    addi t0, a0, 32
    sltiu s7, t0, 32
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, zero
    bgeu t1, zero, .Lk10117
    addi s7, s7, 1
.Lk10117:
    bnez s7, eita_oog
    li   s8, 3
    li   s9, 0
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx5062
    bltu t2, t0, eita_oog
.Lx5062:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx5067
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx5067:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    addi t4, a0, 32
    sltiu s7, t4, 32
    add  t5, a1, s7
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm5085
    bne  s11, t5, .Lx5085
    bltu s10, t4, .Lm5085
.Lx5085:
    mv   s10, s10
    mv   s11, s11
    j    .Ln5085
.Lm5085:
    mv   s10, t4
    mv   s11, t5
.Ln5085:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    lw   t2, 40(s0)
    lw   t3, 44(s0)
    add  t2, t2, a0
    sltu s7, t2, a0
    add  t3, t3, s7
    add  t3, t3, a1
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    li   t2, 0xff00ff
    srli s7, s6, 8
    and  s7, s7, t2
    and  t3, s6, t2
    slli t3, t3, 8
    or   t3, t3, s7
    slli s7, t3, 16
    srli t3, t3, 16
    or   t3, t3, s7
    sw   t3, 616(s0)
    srli s7, t6, 8
    and  s7, s7, t2
    and  t3, t6, t2
    slli t3, t3, 8
    or   t3, t3, s7
    slli s7, t3, 16
    srli t3, t3, 16
    or   t3, t3, s7
    mv   t0, t3
    lw   t3, 616(s0)
    mv   t1, t3
    lw   t2, 608(s0)
    lw   t3, 612(s0)
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, s6, 8
    and  s7, s7, t0
    and  t1, s6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, t6, 8
    and  s7, s7, t0
    and  t1, t6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   t4, t1
    lw   t1, 616(s0)
    mv   t5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, s6, 8
    and  s7, s7, t0
    and  t1, s6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, t6, 8
    and  s7, s7, t0
    and  t1, t6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   s8, t1
    lw   t1, 616(s0)
    mv   s9, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, s6, 8
    and  s7, s7, t0
    and  t1, s6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, t6, 8
    and  s7, s7, t0
    and  t1, t6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   s10, t1
    lw   t1, 616(s0)
    mv   s11, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t3, 608(s0)
    sb   t0, 0(t2)
    srli t3, t0, 8
    sb   t3, 1(t2)
    srli t3, t0, 16
    sb   t3, 2(t2)
    srli t3, t0, 24
    sb   t3, 3(t2)
    sb   t1, 4(t2)
    srli t3, t1, 8
    sb   t3, 5(t2)
    srli t3, t1, 16
    sb   t3, 6(t2)
    srli t3, t1, 24
    sb   t3, 7(t2)
    lw   t3, 608(s0)
    sw   t0, 608(s0)
    sb   t4, 8(t2)
    srli t0, t4, 8
    sb   t0, 9(t2)
    srli t0, t4, 16
    sb   t0, 10(t2)
    srli t0, t4, 24
    sb   t0, 11(t2)
    sb   t5, 12(t2)
    srli t0, t5, 8
    sb   t0, 13(t2)
    srli t0, t5, 16
    sb   t0, 14(t2)
    srli t0, t5, 24
    sb   t0, 15(t2)
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sb   s8, 16(t2)
    srli t0, s8, 8
    sb   t0, 17(t2)
    srli t0, s8, 16
    sb   t0, 18(t2)
    srli t0, s8, 24
    sb   t0, 19(t2)
    sb   s9, 20(t2)
    srli t0, s9, 8
    sb   t0, 21(t2)
    srli t0, s9, 16
    sb   t0, 22(t2)
    srli t0, s9, 24
    sb   t0, 23(t2)
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sb   s10, 24(t2)
    srli t0, s10, 8
    sb   t0, 25(t2)
    srli t0, s10, 16
    sb   t0, 26(t2)
    srli t0, s10, 24
    sb   t0, 27(t2)
    sb   s11, 28(t2)
    srli t0, s11, 8
    sb   t0, 29(t2)
    srli t0, s11, 16
    sb   t0, 30(t2)
    srli t0, s11, 24
    sb   t0, 31(t2)
    lw   t0, 608(s0)
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_mstore8
.p2align 2
eita_handler_mstore8:
    li   s7, 64
    bnez zero, .Lx5166
    bltu s2, s7, eita_stack_underflow
.Lx5166:
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    addi t0, a0, 1
    sltiu s7, t0, 1
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, zero
    bgeu t1, zero, .Lk10341
    addi s7, s7, 1
.Lk10341:
    bnez s7, eita_oog
    li   s8, 3
    li   s9, 0
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx5174
    bltu t2, t0, eita_oog
.Lx5174:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx5179
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx5179:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t2, 40(s0)
    lw   t3, 44(s0)
    addi t4, a0, 1
    sltiu s7, t4, 1
    add  t5, a1, s7
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm5198
    bne  s11, t5, .Lx5198
    bltu s10, t4, .Lm5198
.Lx5198:
    mv   s10, s10
    mv   s11, s11
    j    .Ln5198
.Lm5198:
    mv   s10, t4
    mv   s11, t5
.Ln5198:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  s7, t2, a0
    sb   s6, 0(s7)
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    ret
.text
.globl eita_handler_return
.p2align 2
eita_handler_return:
    li   s7, 64
    bnez zero, .Lx5262
    bltu s2, s7, eita_stack_underflow
.Lx5262:
    sltiu s7, s1, 1
    addi s1, s1, -1
    sub  zero, zero, s7
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lror0
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk10567
    addi s7, s7, 1
.Lk10567:
    bnez s7, eita_oog
    j    .Lror1
.Lror0:
    li   t0, 0
    li   t1, 0
.Lror1:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx5292
    bltu t2, t0, eita_oog
.Lx5292:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx5297
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx5297:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    sw   s6, 120(s0)
    sw   t6, 124(s0)
    lw   t2, 40(s0)
    lw   t3, 44(s0)
    add  t2, t2, a0
    sltu s7, t2, a0
    add  t3, t3, s7
    add  t3, t3, a1
    sw   t2, 112(s0)
    sw   t3, 116(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm5320
    bne  s11, t5, .Lx5320
    bltu s10, t4, .Lm5320
.Lx5320:
    mv   s10, s10
    mv   s11, s11
    j    .Ln5320
.Lm5320:
    mv   s10, t4
    mv   s11, t5
.Ln5320:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    li   t2, 1
    li   t3, 0
    sb   t2, 128(s0)
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    j    eita_sync_and_ret
.text
.globl eita_handler_revert
.p2align 2
eita_handler_revert:
    li   s7, 64
    bnez zero, .Lx5400
    bltu s2, s7, eita_stack_underflow
.Lx5400:
    sltiu s7, s1, 1
    addi s1, s1, -1
    sub  zero, zero, s7
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   s10, 0(t2)
    lw   s11, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    or   s7, s10, s11
    beqz s7, .Lrov0
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    lw   s8, 24(t2)
    lw   s9, 28(t2)
    or   t4, t4, s8
    or   t5, t5, s9
    or   s7, t4, t5
    bnez s7, eita_oog
    lw   s8, 0(t2)
    lw   s9, 4(t2)
    add  t0, s8, s10
    sltu s7, t0, s10
    add  t1, s9, s7
    sltu s7, t1, s7
    add  t1, t1, s11
    bgeu t1, s11, .Lk10843
    addi s7, s7, 1
.Lk10843:
    bnez s7, eita_oog
    j    .Lrov1
.Lrov0:
    li   t0, 0
    li   t1, 0
.Lrov1:
    li   s8, 0
    li   s9, 0
    or   s7, t0, t1
    beqz s7, 4f
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx5430
    bltu t2, t0, eita_oog
.Lx5430:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx5435
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx5435:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
4:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    sw   s6, 120(s0)
    sw   t6, 124(s0)
    lw   t2, 40(s0)
    lw   t3, 44(s0)
    add  t2, t2, a0
    sltu s7, t2, a0
    add  t3, t3, s7
    add  t3, t3, a1
    sw   t2, 112(s0)
    sw   t3, 116(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm5458
    bne  s11, t5, .Lx5458
    bltu s10, t4, .Lm5458
.Lx5458:
    mv   s10, s10
    mv   s11, s11
    j    .Ln5458
.Lm5458:
    mv   s10, t4
    mv   s11, t5
.Ln5458:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    li   t2, 1
    li   t3, 0
    sb   t2, 128(s0)
    sb   t2, 129(s0)
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    j    eita_sync_and_ret
.text
.globl eita_handler_jump
.p2align 2
eita_handler_jump:
    li   s7, 32
    bnez zero, .Lx5540
    bltu s2, s7, eita_stack_underflow
.Lx5540:
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_invalid_jump
    lw   t2, 72(s0)
    lw   t3, 76(s0)
    bltu a1, t3, .Lx5545
    bne  t3, a1, eita_invalid_jump
    bgeu a0, t2, eita_invalid_jump
.Lx5545:
    lw   t2, 136(s0)
    lw   t3, 140(s0)
    add  s7, t2, a0
    lbu  t2, 0(s7)
    li   t3, 0
    li   s7, 1
    bne  t2, s7, eita_invalid_jump
    mv   s1, a0
    mv   zero, a1
    sltiu s7, s2, 32
    addi s2, s2, -32
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 8
    addi s5, s5, -8
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_jumpi
.p2align 2
eita_handler_jumpi:
    li   s7, 64
    bnez zero, .Lx5588
    bltu s2, s7, eita_stack_underflow
.Lx5588:
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    mv   t4, s6
    mv   t5, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t4, t4, s6
    or   t5, t5, t6
    or   t2, t2, t4
    or   t3, t3, t5
    or   s7, t2, t3
    beqz s7, eita_jumpi_fallthrough
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_invalid_jump
    lw   t2, 72(s0)
    lw   t3, 76(s0)
    bltu a1, t3, .Lx5597
    bne  t3, a1, eita_invalid_jump
    bgeu a0, t2, eita_invalid_jump
.Lx5597:
    lw   t2, 136(s0)
    lw   t3, 140(s0)
    add  s7, t2, a0
    lbu  t2, 0(s7)
    li   t3, 0
    li   s7, 1
    bne  t2, s7, eita_invalid_jump
    mv   s1, a0
    mv   zero, a1
eita_jumpi_pop:
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 10
    addi s5, s5, -10
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
eita_jumpi_fallthrough:
    j    eita_jumpi_pop
.text
.globl eita_handler_tstore
.p2align 2
eita_handler_tstore:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 64
    bnez zero, .Lx5652
    bltu s2, s7, eita_stack_underflow
.Lx5652:
    li   t2, 100
    li   t3, 0
    sltu s7, s5, t2
    sub  s5, s5, t2
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t3
    sub  zero, zero, t3
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    lw   s8, 504(s0)
    lw   s9, 508(s0)
    sw   t0, 608(s0)
    lbu  s10, 64(s8)
    lbu  t0, 65(s8)
    slli t0, t0, 8
    or   s10, s10, t0
    lbu  t0, 66(s8)
    slli t0, t0, 16
    or   s10, s10, t0
    lbu  t0, 67(s8)
    slli t0, t0, 24
    or   s10, s10, t0
    lbu  s11, 68(s8)
    lbu  t0, 69(s8)
    slli t0, t0, 8
    or   s11, s11, t0
    lbu  t0, 70(s8)
    slli t0, t0, 16
    or   s11, s11, t0
    lbu  t0, 71(s8)
    slli t0, t0, 24
    or   s11, s11, t0
    lw   t0, 608(s0)
    addi t4, s0, 144
    sltiu s7, t4, 144
    add  t5, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s2, 64
    addi a0, s2, -64
    sub  a1, zero, s7
    add  a0, a0, s3
    sltu s7, a0, s3
    add  a1, a1, s7
    add  a1, a1, zero
    addi sp, sp, -16
    sw   ra, 0(sp)
    call eita_ts_tstore
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    ret
.text
.globl eita_handler_push0
.p2align 2
eita_handler_push0:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 2
    addi s5, s5, -2
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push1
.p2align 2
eita_handler_push1:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a1, 24
    li   a1, 0
    addi s1, s1, 1
    sltiu s7, s1, 1
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push2
.p2align 2
eita_handler_push2:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a1, 16
    li   a1, 0
    addi s1, s1, 2
    sltiu s7, s1, 2
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push3
.p2align 2
eita_handler_push3:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a1, 8
    li   a1, 0
    addi s1, s1, 3
    sltiu s7, s1, 3
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push4
.p2align 2
eita_handler_push4:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a1, 0
    li   a1, 0
    addi s1, s1, 4
    sltiu s7, s1, 4
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push5
.p2align 2
eita_handler_push5:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a0, 24
    slli s7, a1, 8
    or   a0, a0, s7
    srli a1, a1, 24
    addi s1, s1, 5
    sltiu s7, s1, 5
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push6
.p2align 2
eita_handler_push6:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a0, 16
    slli s7, a1, 16
    or   a0, a0, s7
    srli a1, a1, 16
    addi s1, s1, 6
    sltiu s7, s1, 6
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push7
.p2align 2
eita_handler_push7:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a0, a0, 8
    slli s7, a1, 24
    or   a0, a0, s7
    srli a1, a1, 8
    addi s1, s1, 7
    sltiu s7, s1, 7
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push8
.p2align 2
eita_handler_push8:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 8
    sltiu s7, s1, 8
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push9
.p2align 2
eita_handler_push9:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a3, 24
    li   a3, 0
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 9
    sltiu s7, s1, 9
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push10
.p2align 2
eita_handler_push10:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a3, 16
    li   a3, 0
    addi t4, t4, 2
    sltiu s7, t4, 2
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 10
    sltiu s7, s1, 10
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push11
.p2align 2
eita_handler_push11:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a3, 8
    li   a3, 0
    addi t4, t4, 3
    sltiu s7, t4, 3
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 11
    sltiu s7, s1, 11
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push12
.p2align 2
eita_handler_push12:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a3, 0
    li   a3, 0
    addi t4, t4, 4
    sltiu s7, t4, 4
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 12
    sltiu s7, s1, 12
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push13
.p2align 2
eita_handler_push13:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a2, 24
    slli s7, a3, 8
    or   a2, a2, s7
    srli a3, a3, 24
    addi t4, t4, 5
    sltiu s7, t4, 5
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 13
    sltiu s7, s1, 13
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push14
.p2align 2
eita_handler_push14:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a2, 16
    slli s7, a3, 16
    or   a2, a2, s7
    srli a3, a3, 16
    addi t4, t4, 6
    sltiu s7, t4, 6
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 14
    sltiu s7, s1, 14
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push15
.p2align 2
eita_handler_push15:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a2, a2, 8
    slli s7, a3, 24
    or   a2, a2, s7
    srli a3, a3, 8
    addi t4, t4, 7
    sltiu s7, t4, 7
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a0, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 15
    sltiu s7, s1, 15
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push16
.p2align 2
eita_handler_push16:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 16
    sltiu s7, s1, 16
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push17
.p2align 2
eita_handler_push17:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a5, 24
    li   a5, 0
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 17
    sltiu s7, s1, 17
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push18
.p2align 2
eita_handler_push18:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a5, 16
    li   a5, 0
    addi t4, t4, 2
    sltiu s7, t4, 2
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 18
    sltiu s7, s1, 18
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push19
.p2align 2
eita_handler_push19:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a5, 8
    li   a5, 0
    addi t4, t4, 3
    sltiu s7, t4, 3
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 19
    sltiu s7, s1, 19
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push20
.p2align 2
eita_handler_push20:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a5, 0
    li   a5, 0
    addi t4, t4, 4
    sltiu s7, t4, 4
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 20
    sltiu s7, s1, 20
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push21
.p2align 2
eita_handler_push21:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a4, 24
    slli s7, a5, 8
    or   a4, a4, s7
    srli a5, a5, 24
    addi t4, t4, 5
    sltiu s7, t4, 5
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 21
    sltiu s7, s1, 21
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push22
.p2align 2
eita_handler_push22:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a4, 16
    slli s7, a5, 16
    or   a4, a4, s7
    srli a5, a5, 16
    addi t4, t4, 6
    sltiu s7, t4, 6
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 22
    sltiu s7, s1, 22
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push23
.p2align 2
eita_handler_push23:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a4, a4, 8
    slli s7, a5, 24
    or   a4, a4, s7
    srli a5, a5, 8
    addi t4, t4, 7
    sltiu s7, t4, 7
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a2, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 23
    sltiu s7, s1, 23
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push24
.p2align 2
eita_handler_push24:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 24
    sltiu s7, s1, 24
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push25
.p2align 2
eita_handler_push25:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a7, 24
    li   a7, 0
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 25
    sltiu s7, s1, 25
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push26
.p2align 2
eita_handler_push26:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a7, 16
    li   a7, 0
    addi t4, t4, 2
    sltiu s7, t4, 2
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 26
    sltiu s7, s1, 26
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push27
.p2align 2
eita_handler_push27:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a7, 8
    li   a7, 0
    addi t4, t4, 3
    sltiu s7, t4, 3
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 27
    sltiu s7, s1, 27
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push28
.p2align 2
eita_handler_push28:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a7, 0
    li   a7, 0
    addi t4, t4, 4
    sltiu s7, t4, 4
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 28
    sltiu s7, s1, 28
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push29
.p2align 2
eita_handler_push29:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a6, 24
    slli s7, a7, 8
    or   a6, a6, s7
    srli a7, a7, 24
    addi t4, t4, 5
    sltiu s7, t4, 5
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 29
    sltiu s7, s1, 29
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push30
.p2align 2
eita_handler_push30:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a6, 16
    slli s7, a7, 16
    or   a6, a6, s7
    srli a7, a7, 16
    addi t4, t4, 6
    sltiu s7, t4, 6
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 30
    sltiu s7, s1, 30
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push31
.p2align 2
eita_handler_push31:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    srli a6, a6, 8
    slli s7, a7, 24
    or   a6, a6, s7
    srli a7, a7, 8
    addi t4, t4, 7
    sltiu s7, t4, 7
    add  t5, t5, s7
    sw   t0, 608(s0)
    lbu  a4, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 31
    sltiu s7, s1, 31
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_push32
.p2align 2
eita_handler_push32:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   a0, 0
    li   a1, 0
    li   a2, 0
    li   a3, 0
    li   a4, 0
    li   a5, 0
    li   a6, 0
    li   a7, 0
    add  t4, s4, s1
    sltu s7, t4, s1
    add  t5, zero, s7
    add  t5, t5, zero
    sw   t0, 608(s0)
    lbu  a6, 0(t4)
    lbu  t0, 1(t4)
    slli t0, t0, 8
    or   a6, a6, t0
    lbu  t0, 2(t4)
    slli t0, t0, 16
    or   a6, a6, t0
    lbu  t0, 3(t4)
    slli t0, t0, 24
    or   a6, a6, t0
    lbu  a7, 4(t4)
    lbu  t0, 5(t4)
    slli t0, t0, 8
    or   a7, a7, t0
    lbu  t0, 6(t4)
    slli t0, t0, 16
    or   a7, a7, t0
    lbu  t0, 7(t4)
    slli t0, t0, 24
    or   a7, a7, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a6, 8
    and  s7, s7, t0
    and  t1, a6, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a7, 8
    and  s7, s7, t0
    and  t1, a7, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a6, t1
    lw   t1, 616(s0)
    mv   a7, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a4, 8(t4)
    lbu  t0, 9(t4)
    slli t0, t0, 8
    or   a4, a4, t0
    lbu  t0, 10(t4)
    slli t0, t0, 16
    or   a4, a4, t0
    lbu  t0, 11(t4)
    slli t0, t0, 24
    or   a4, a4, t0
    lbu  a5, 12(t4)
    lbu  t0, 13(t4)
    slli t0, t0, 8
    or   a5, a5, t0
    lbu  t0, 14(t4)
    slli t0, t0, 16
    or   a5, a5, t0
    lbu  t0, 15(t4)
    slli t0, t0, 24
    or   a5, a5, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a4, 8
    and  s7, s7, t0
    and  t1, a4, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a5, 8
    and  s7, s7, t0
    and  t1, a5, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a4, t1
    lw   t1, 616(s0)
    mv   a5, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a2, 16(t4)
    lbu  t0, 17(t4)
    slli t0, t0, 8
    or   a2, a2, t0
    lbu  t0, 18(t4)
    slli t0, t0, 16
    or   a2, a2, t0
    lbu  t0, 19(t4)
    slli t0, t0, 24
    or   a2, a2, t0
    lbu  a3, 20(t4)
    lbu  t0, 21(t4)
    slli t0, t0, 8
    or   a3, a3, t0
    lbu  t0, 22(t4)
    slli t0, t0, 16
    or   a3, a3, t0
    lbu  t0, 23(t4)
    slli t0, t0, 24
    or   a3, a3, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a2, 8
    and  s7, s7, t0
    and  t1, a2, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a3, 8
    and  s7, s7, t0
    and  t1, a3, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a2, t1
    lw   t1, 616(s0)
    mv   a3, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    sw   t0, 608(s0)
    lbu  a0, 24(t4)
    lbu  t0, 25(t4)
    slli t0, t0, 8
    or   a0, a0, t0
    lbu  t0, 26(t4)
    slli t0, t0, 16
    or   a0, a0, t0
    lbu  t0, 27(t4)
    slli t0, t0, 24
    or   a0, a0, t0
    lbu  a1, 28(t4)
    lbu  t0, 29(t4)
    slli t0, t0, 8
    or   a1, a1, t0
    lbu  t0, 30(t4)
    slli t0, t0, 16
    or   a1, a1, t0
    lbu  t0, 31(t4)
    slli t0, t0, 24
    or   a1, a1, t0
    lw   t0, 608(s0)
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    li   t0, 0xff00ff
    srli s7, a0, 8
    and  s7, s7, t0
    and  t1, a0, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    sw   t1, 616(s0)
    srli s7, a1, 8
    and  s7, s7, t0
    and  t1, a1, t0
    slli t1, t1, 8
    or   t1, t1, s7
    slli s7, t1, 16
    srli t1, t1, 16
    or   t1, t1, s7
    mv   a0, t1
    lw   t1, 616(s0)
    mv   a1, t1
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    addi s1, s1, 32
    sltiu s7, s1, 32
    add  zero, zero, s7
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_log0
.p2align 2
eita_handler_log0:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 64
    bnez zero, .Lx7240
    bltu s2, s7, eita_stack_underflow
.Lx7240:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    li   s8, 375
    li   s9, 0
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   t0, s6
    mv   t1, t6
    slli t1, t1, 3
    srli s7, t0, 29
    or   t1, t1, s7
    slli t0, t0, 3
    add  s8, s8, t0
    sltu s7, s8, t0
    add  s9, s9, s7
    add  s9, s9, t1
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   s7, s6, t6
    beqz s7, 4f
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t0, a0, s6
    sltu s7, t0, s6
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t6
    bgeu t1, t6, .Lk14513
    addi s7, s7, 1
.Lk14513:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx7259
    bltu t2, t0, eita_oog
.Lx7259:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx7264
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx7264:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
4:
    lw   t2, 504(s0)
    lw   t3, 508(s0)
    sw   t0, 608(s0)
    lbu  t4, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   t4, t4, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   t4, t4, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   t4, t4, t0
    lbu  t5, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   t5, t5, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   t5, t5, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   t5, t5, t0
    lw   t0, 608(s0)
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    sb   t4, 8(t2)
    srli t0, t4, 8
    sb   t0, 9(t2)
    srli t0, t4, 16
    sb   t0, 10(t2)
    srli t0, t4, 24
    sb   t0, 11(t2)
    sb   t5, 12(t2)
    srli t0, t5, 8
    sb   t0, 13(t2)
    srli t0, t5, 16
    sb   t0, 14(t2)
    srli t0, t5, 24
    sb   t0, 15(t2)
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm7285
    bne  s11, t5, .Lx7285
    bltu s10, t4, .Lm7285
.Lx7285:
    mv   s10, s10
    mv   s11, s11
    j    .Ln7285
.Lm7285:
    mv   s10, t4
    mv   s11, t5
.Ln7285:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    sltiu s7, s2, 64
    addi s2, s2, -64
    sub  zero, zero, s7
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    mv   t3, t0
    lbu  t0, 72(t3)
    lbu  t2, 73(t3)
    slli t2, t2, 8
    or   t0, t0, t2
    lbu  t2, 74(t3)
    slli t2, t2, 16
    or   t0, t0, t2
    lbu  t2, 75(t3)
    slli t2, t2, 24
    or   t0, t0, t2
    lbu  t1, 76(t3)
    lbu  t2, 77(t3)
    slli t2, t2, 8
    or   t1, t1, t2
    lbu  t2, 78(t3)
    slli t2, t2, 16
    or   t1, t1, t2
    lbu  t2, 79(t3)
    slli t2, t2, 24
    or   t1, t1, t2
    lw   t3, 612(s0)
    lw   t2, 608(s0)
    or   s7, t0, t1
    beqz s7, 7f
    lw   s10, 504(s0)
    lw   s11, 508(s0)
    addi s8, s0, 144
    sltiu s7, s8, 144
    add  s9, zero, s7
    add  t2, s3, s2
    sltu s7, t2, s2
    add  t3, zero, s7
    add  t3, t3, zero
    addi t4, s2, 32
    sltiu s7, t4, 32
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   t5, 4(t4)
    lw   t4, 0(t4)
    lw   a0, 40(s0)
    lw   a1, 44(s0)
    add  a0, a0, t4
    sltu s7, a0, t4
    add  a1, a1, s7
    add  a1, a1, t5
    addi t4, s2, 0
    sltiu s7, t4, 0
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   a2, 0(t4)
    lw   a3, 4(t4)
    li   a2, 0
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
7:
    li   s7, 32
    blt  zero, zero, 5f
    bnez zero, .Lx7307
    bltu s2, s7, 5f
.Lx7307:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
5:
    ret
.text
.globl eita_handler_log1
.p2align 2
eita_handler_log1:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 96
    bnez zero, .Lx7404
    bltu s2, s7, eita_stack_underflow
.Lx7404:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    li   s8, 750
    li   s9, 0
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   t0, s6
    mv   t1, t6
    slli t1, t1, 3
    srli s7, t0, 29
    or   t1, t1, s7
    slli t0, t0, 3
    add  s8, s8, t0
    sltu s7, s8, t0
    add  s9, s9, s7
    add  s9, s9, t1
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   s7, s6, t6
    beqz s7, 4f
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t0, a0, s6
    sltu s7, t0, s6
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t6
    bgeu t1, t6, .Lk14841
    addi s7, s7, 1
.Lk14841:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx7423
    bltu t2, t0, eita_oog
.Lx7423:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx7428
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx7428:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
4:
    lw   t2, 504(s0)
    lw   t3, 508(s0)
    sw   t0, 608(s0)
    lbu  t4, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   t4, t4, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   t4, t4, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   t4, t4, t0
    lbu  t5, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   t5, t5, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   t5, t5, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   t5, t5, t0
    lw   t0, 608(s0)
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    sb   t4, 8(t2)
    srli t0, t4, 8
    sb   t0, 9(t2)
    srli t0, t4, 16
    sb   t0, 10(t2)
    srli t0, t4, 24
    sb   t0, 11(t2)
    sb   t5, 12(t2)
    srli t0, t5, 8
    sb   t0, 13(t2)
    srli t0, t5, 16
    sb   t0, 14(t2)
    srli t0, t5, 24
    sb   t0, 15(t2)
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm7449
    bne  s11, t5, .Lx7449
    bltu s10, t4, .Lm7449
.Lx7449:
    mv   s10, s10
    mv   s11, s11
    j    .Ln7449
.Lm7449:
    mv   s10, t4
    mv   s11, t5
.Ln7449:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    sltiu s7, s2, 96
    addi s2, s2, -96
    sub  zero, zero, s7
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    mv   t3, t0
    lbu  t0, 72(t3)
    lbu  t2, 73(t3)
    slli t2, t2, 8
    or   t0, t0, t2
    lbu  t2, 74(t3)
    slli t2, t2, 16
    or   t0, t0, t2
    lbu  t2, 75(t3)
    slli t2, t2, 24
    or   t0, t0, t2
    lbu  t1, 76(t3)
    lbu  t2, 77(t3)
    slli t2, t2, 8
    or   t1, t1, t2
    lbu  t2, 78(t3)
    slli t2, t2, 16
    or   t1, t1, t2
    lbu  t2, 79(t3)
    slli t2, t2, 24
    or   t1, t1, t2
    lw   t3, 612(s0)
    lw   t2, 608(s0)
    or   s7, t0, t1
    beqz s7, 7f
    lw   s10, 504(s0)
    lw   s11, 508(s0)
    addi s8, s0, 144
    sltiu s7, s8, 144
    add  s9, zero, s7
    add  t2, s3, s2
    sltu s7, t2, s2
    add  t3, zero, s7
    add  t3, t3, zero
    addi t4, s2, 64
    sltiu s7, t4, 64
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   t5, 4(t4)
    lw   t4, 0(t4)
    lw   a0, 40(s0)
    lw   a1, 44(s0)
    add  a0, a0, t4
    sltu s7, a0, t4
    add  a1, a1, s7
    add  a1, a1, t5
    addi t4, s2, 32
    sltiu s7, t4, 32
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   a2, 0(t4)
    lw   a3, 4(t4)
    li   a2, 1
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
7:
    li   s7, 32
    blt  zero, zero, 5f
    bnez zero, .Lx7471
    bltu s2, s7, 5f
.Lx7471:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
5:
    ret
.text
.globl eita_handler_log2
.p2align 2
eita_handler_log2:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 128
    bnez zero, .Lx7568
    bltu s2, s7, eita_stack_underflow
.Lx7568:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    li   s8, 1125
    li   s9, 0
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   t0, s6
    mv   t1, t6
    slli t1, t1, 3
    srli s7, t0, 29
    or   t1, t1, s7
    slli t0, t0, 3
    add  s8, s8, t0
    sltu s7, s8, t0
    add  s9, s9, s7
    add  s9, s9, t1
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   s7, s6, t6
    beqz s7, 4f
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t0, a0, s6
    sltu s7, t0, s6
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t6
    bgeu t1, t6, .Lk15169
    addi s7, s7, 1
.Lk15169:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx7587
    bltu t2, t0, eita_oog
.Lx7587:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx7592
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx7592:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
4:
    lw   t2, 504(s0)
    lw   t3, 508(s0)
    sw   t0, 608(s0)
    lbu  t4, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   t4, t4, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   t4, t4, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   t4, t4, t0
    lbu  t5, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   t5, t5, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   t5, t5, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   t5, t5, t0
    lw   t0, 608(s0)
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    sb   t4, 8(t2)
    srli t0, t4, 8
    sb   t0, 9(t2)
    srli t0, t4, 16
    sb   t0, 10(t2)
    srli t0, t4, 24
    sb   t0, 11(t2)
    sb   t5, 12(t2)
    srli t0, t5, 8
    sb   t0, 13(t2)
    srli t0, t5, 16
    sb   t0, 14(t2)
    srli t0, t5, 24
    sb   t0, 15(t2)
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm7613
    bne  s11, t5, .Lx7613
    bltu s10, t4, .Lm7613
.Lx7613:
    mv   s10, s10
    mv   s11, s11
    j    .Ln7613
.Lm7613:
    mv   s10, t4
    mv   s11, t5
.Ln7613:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    sltiu s7, s2, 128
    addi s2, s2, -128
    sub  zero, zero, s7
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    mv   t3, t0
    lbu  t0, 72(t3)
    lbu  t2, 73(t3)
    slli t2, t2, 8
    or   t0, t0, t2
    lbu  t2, 74(t3)
    slli t2, t2, 16
    or   t0, t0, t2
    lbu  t2, 75(t3)
    slli t2, t2, 24
    or   t0, t0, t2
    lbu  t1, 76(t3)
    lbu  t2, 77(t3)
    slli t2, t2, 8
    or   t1, t1, t2
    lbu  t2, 78(t3)
    slli t2, t2, 16
    or   t1, t1, t2
    lbu  t2, 79(t3)
    slli t2, t2, 24
    or   t1, t1, t2
    lw   t3, 612(s0)
    lw   t2, 608(s0)
    or   s7, t0, t1
    beqz s7, 7f
    lw   s10, 504(s0)
    lw   s11, 508(s0)
    addi s8, s0, 144
    sltiu s7, s8, 144
    add  s9, zero, s7
    add  t2, s3, s2
    sltu s7, t2, s2
    add  t3, zero, s7
    add  t3, t3, zero
    addi t4, s2, 96
    sltiu s7, t4, 96
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   t5, 4(t4)
    lw   t4, 0(t4)
    lw   a0, 40(s0)
    lw   a1, 44(s0)
    add  a0, a0, t4
    sltu s7, a0, t4
    add  a1, a1, s7
    add  a1, a1, t5
    addi t4, s2, 64
    sltiu s7, t4, 64
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   a2, 0(t4)
    lw   a3, 4(t4)
    li   a2, 2
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
7:
    li   s7, 32
    blt  zero, zero, 5f
    bnez zero, .Lx7635
    bltu s2, s7, 5f
.Lx7635:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
5:
    ret
.text
.globl eita_handler_log3
.p2align 2
eita_handler_log3:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 160
    bnez zero, .Lx7732
    bltu s2, s7, eita_stack_underflow
.Lx7732:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    li   s8, 1500
    li   s9, 0
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   t0, s6
    mv   t1, t6
    slli t1, t1, 3
    srli s7, t0, 29
    or   t1, t1, s7
    slli t0, t0, 3
    add  s8, s8, t0
    sltu s7, s8, t0
    add  s9, s9, s7
    add  s9, s9, t1
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   s7, s6, t6
    beqz s7, 4f
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t0, a0, s6
    sltu s7, t0, s6
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t6
    bgeu t1, t6, .Lk15497
    addi s7, s7, 1
.Lk15497:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx7751
    bltu t2, t0, eita_oog
.Lx7751:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx7756
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx7756:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
4:
    lw   t2, 504(s0)
    lw   t3, 508(s0)
    sw   t0, 608(s0)
    lbu  t4, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   t4, t4, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   t4, t4, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   t4, t4, t0
    lbu  t5, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   t5, t5, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   t5, t5, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   t5, t5, t0
    lw   t0, 608(s0)
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    sb   t4, 8(t2)
    srli t0, t4, 8
    sb   t0, 9(t2)
    srli t0, t4, 16
    sb   t0, 10(t2)
    srli t0, t4, 24
    sb   t0, 11(t2)
    sb   t5, 12(t2)
    srli t0, t5, 8
    sb   t0, 13(t2)
    srli t0, t5, 16
    sb   t0, 14(t2)
    srli t0, t5, 24
    sb   t0, 15(t2)
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm7777
    bne  s11, t5, .Lx7777
    bltu s10, t4, .Lm7777
.Lx7777:
    mv   s10, s10
    mv   s11, s11
    j    .Ln7777
.Lm7777:
    mv   s10, t4
    mv   s11, t5
.Ln7777:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    sltiu s7, s2, 160
    addi s2, s2, -160
    sub  zero, zero, s7
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    mv   t3, t0
    lbu  t0, 72(t3)
    lbu  t2, 73(t3)
    slli t2, t2, 8
    or   t0, t0, t2
    lbu  t2, 74(t3)
    slli t2, t2, 16
    or   t0, t0, t2
    lbu  t2, 75(t3)
    slli t2, t2, 24
    or   t0, t0, t2
    lbu  t1, 76(t3)
    lbu  t2, 77(t3)
    slli t2, t2, 8
    or   t1, t1, t2
    lbu  t2, 78(t3)
    slli t2, t2, 16
    or   t1, t1, t2
    lbu  t2, 79(t3)
    slli t2, t2, 24
    or   t1, t1, t2
    lw   t3, 612(s0)
    lw   t2, 608(s0)
    or   s7, t0, t1
    beqz s7, 7f
    lw   s10, 504(s0)
    lw   s11, 508(s0)
    addi s8, s0, 144
    sltiu s7, s8, 144
    add  s9, zero, s7
    add  t2, s3, s2
    sltu s7, t2, s2
    add  t3, zero, s7
    add  t3, t3, zero
    addi t4, s2, 128
    sltiu s7, t4, 128
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   t5, 4(t4)
    lw   t4, 0(t4)
    lw   a0, 40(s0)
    lw   a1, 44(s0)
    add  a0, a0, t4
    sltu s7, a0, t4
    add  a1, a1, s7
    add  a1, a1, t5
    addi t4, s2, 96
    sltiu s7, t4, 96
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   a2, 0(t4)
    lw   a3, 4(t4)
    li   a2, 3
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
7:
    li   s7, 32
    blt  zero, zero, 5f
    bnez zero, .Lx7799
    bltu s2, s7, 5f
.Lx7799:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
5:
    ret
.text
.globl eita_handler_log4
.p2align 2
eita_handler_log4:
    lbu  t2, 130(s0)
    li   t3, 0
    bnez t2, eita_static_violation
    li   s7, 192
    bnez zero, .Lx7896
    bltu s2, s7, eita_stack_underflow
.Lx7896:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    add  t6, s3, s2
    lw   s6, -56(t6)
    lw   t6, -52(t6)
    mv   t2, s6
    mv   t3, t6
    add  t6, s3, s2
    lw   s6, -48(t6)
    lw   t6, -44(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    add  t6, s3, s2
    lw   s6, -40(t6)
    lw   t6, -36(t6)
    or   t2, t2, s6
    or   t3, t3, t6
    or   s7, t2, t3
    bnez s7, eita_oog
    li   s8, 1875
    li   s9, 0
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    mv   t0, s6
    mv   t1, t6
    slli t1, t1, 3
    srli s7, t0, 29
    or   t1, t1, s7
    slli t0, t0, 3
    add  s8, s8, t0
    sltu s7, s8, t0
    add  s9, s9, s7
    add  s9, s9, t1
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    or   s7, s6, t6
    beqz s7, 4f
    or   t2, a2, a4
    or   t3, a3, a5
    or   t2, t2, a6
    or   t3, t3, a7
    or   s7, t2, t3
    bnez s7, eita_oog
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t0, a0, s6
    sltu s7, t0, s6
    add  t1, a1, s7
    sltu s7, t1, s7
    add  t1, t1, t6
    bgeu t1, t6, .Lk15825
    addi s7, s7, 1
.Lk15825:
    bnez s7, eita_oog
    lw   t2, 56(s0)
    lw   t3, 60(s0)
    bltu t3, t1, eita_oog
    bne  t3, t1, .Lx7915
    bltu t2, t0, eita_oog
.Lx7915:
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    lw   t4, 48(s0)
    lw   t5, 52(s0)
    srli t4, t4, 5
    slli s7, t5, 27
    or   t4, t4, s7
    srli t5, t5, 5
    bltu t5, t3, .Lx7920
    bne  t3, t5, 7f
    bgeu t4, t2, 7f
.Lx7920:
    mulhu s11, t2, t2
    mul  s10, t2, t2
    mul  s7, t2, t3
    add  s11, s11, s7
    mul  s7, t3, t2
    add  s11, s11, s7
    srli s6, s10, 9
    slli s7, s11, 23
    or   s6, s6, s7
    srli t6, s11, 9
    add  s10, t2, s6
    sltu s7, s10, s6
    add  s11, t3, t6
    add  s11, s11, s7
    slli t6, t3, 1
    srli s7, t2, 31
    or   t6, t6, s7
    slli s6, t2, 1
    add  s10, s10, s6
    sltu s7, s10, s6
    add  s11, s11, t6
    add  s11, s11, s7
    mulhu t3, t4, t4
    mul  t2, t4, t4
    mul  s7, t4, t5
    add  t3, t3, s7
    mul  s7, t5, t4
    add  t3, t3, s7
    srli s6, t2, 9
    slli s7, t3, 23
    or   s6, s6, s7
    srli t6, t3, 9
    add  t2, t4, s6
    sltu s7, t2, s6
    add  t3, t5, t6
    add  t3, t3, s7
    slli t6, t5, 1
    srli s7, t4, 31
    or   t6, t6, s7
    slli s6, t4, 1
    add  t2, t2, s6
    sltu s7, t2, s6
    add  t3, t3, t6
    add  t3, t3, s7
    sltu s7, s10, t2
    sub  s10, s10, t2
    sub  s11, s11, t3
    sub  s11, s11, s7
    add  s8, s8, s10
    sltu s7, s8, s10
    add  s9, s9, s7
    add  s9, s9, s11
    addi t2, t0, 31
    sltiu s7, t2, 31
    add  t3, t1, s7
    srli t2, t2, 5
    slli s7, t3, 27
    or   t2, t2, s7
    srli t3, t3, 5
    slli t3, t3, 5
    srli s7, t2, 27
    or   t3, t3, s7
    slli t2, t2, 5
    sw   t2, 48(s0)
    sw   t3, 52(s0)
7:
4:
    lw   t2, 504(s0)
    lw   t3, 508(s0)
    sw   t0, 608(s0)
    lbu  t4, 8(t2)
    lbu  t0, 9(t2)
    slli t0, t0, 8
    or   t4, t4, t0
    lbu  t0, 10(t2)
    slli t0, t0, 16
    or   t4, t4, t0
    lbu  t0, 11(t2)
    slli t0, t0, 24
    or   t4, t4, t0
    lbu  t5, 12(t2)
    lbu  t0, 13(t2)
    slli t0, t0, 8
    or   t5, t5, t0
    lbu  t0, 14(t2)
    slli t0, t0, 16
    or   t5, t5, t0
    lbu  t0, 15(t2)
    slli t0, t0, 24
    or   t5, t5, t0
    lw   t0, 608(s0)
    addi t4, t4, 1
    sltiu s7, t4, 1
    add  t5, t5, s7
    sw   t0, 608(s0)
    sb   t4, 8(t2)
    srli t0, t4, 8
    sb   t0, 9(t2)
    srli t0, t4, 16
    sb   t0, 10(t2)
    srli t0, t4, 24
    sb   t0, 11(t2)
    sb   t5, 12(t2)
    srli t0, t5, 8
    sb   t0, 13(t2)
    srli t0, t5, 16
    sb   t0, 14(t2)
    srli t0, t5, 24
    sb   t0, 15(t2)
    lw   t0, 608(s0)
    add  t6, s3, s2
    lw   s6, -64(t6)
    lw   t6, -60(t6)
    add  t4, a0, s6
    sltu s7, t4, s6
    add  t5, a1, s7
    add  t5, t5, t6
    lw   s10, 24(s0)
    lw   s11, 28(s0)
    bltu s11, t5, .Lm7941
    bne  s11, t5, .Lx7941
    bltu s10, t4, .Lm7941
.Lx7941:
    mv   s10, s10
    mv   s11, s11
    j    .Ln7941
.Lm7941:
    mv   s10, t4
    mv   s11, t5
.Ln7941:
    sw   s10, 24(s0)
    sw   s11, 28(s0)
    sltiu s7, s2, 192
    addi s2, s2, -192
    sub  zero, zero, s7
    sltu s7, s5, s8
    sub  s5, s5, s8
    sw   t0, 608(s0)
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, s9
    sub  zero, zero, s9
    or   s7, s7, t0
    lw   t0, 608(s0)
    bnez s7, eita_oog
    lw   t0, 496(s0)
    lw   t1, 500(s0)
    sw   t2, 608(s0)
    sw   t3, 612(s0)
    mv   t3, t0
    lbu  t0, 72(t3)
    lbu  t2, 73(t3)
    slli t2, t2, 8
    or   t0, t0, t2
    lbu  t2, 74(t3)
    slli t2, t2, 16
    or   t0, t0, t2
    lbu  t2, 75(t3)
    slli t2, t2, 24
    or   t0, t0, t2
    lbu  t1, 76(t3)
    lbu  t2, 77(t3)
    slli t2, t2, 8
    or   t1, t1, t2
    lbu  t2, 78(t3)
    slli t2, t2, 16
    or   t1, t1, t2
    lbu  t2, 79(t3)
    slli t2, t2, 24
    or   t1, t1, t2
    lw   t3, 612(s0)
    lw   t2, 608(s0)
    or   s7, t0, t1
    beqz s7, 7f
    lw   s10, 504(s0)
    lw   s11, 508(s0)
    addi s8, s0, 144
    sltiu s7, s8, 144
    add  s9, zero, s7
    add  t2, s3, s2
    sltu s7, t2, s2
    add  t3, zero, s7
    add  t3, t3, zero
    addi t4, s2, 160
    sltiu s7, t4, 160
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   t5, 4(t4)
    lw   t4, 0(t4)
    lw   a0, 40(s0)
    lw   a1, 44(s0)
    add  a0, a0, t4
    sltu s7, a0, t4
    add  a1, a1, s7
    add  a1, a1, t5
    addi t4, s2, 128
    sltiu s7, t4, 128
    add  t5, zero, s7
    add  t4, t4, s3
    sltu s7, t4, s3
    add  t5, t5, s7
    add  t5, t5, zero
    lw   a2, 0(t4)
    lw   a3, 4(t4)
    li   a2, 4
    addi sp, sp, -16
    sw   ra, 0(sp)
    jalr t0
    lw   ra, 0(sp)
    addi sp, sp, 16
    mv   t0, a0
    mv   t1, a1
7:
    li   s7, 32
    blt  zero, zero, 5f
    bnez zero, .Lx7963
    bltu s2, s7, 5f
.Lx7963:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
5:
    ret
.text
.globl eita_handler_dup1
.p2align 2
eita_handler_dup1:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 32
    bnez zero, .Lx8059
    bltu s2, s7, eita_stack_underflow
.Lx8059:
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup2
.p2align 2
eita_handler_dup2:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 64
    bnez zero, .Lx8093
    bltu s2, s7, eita_stack_underflow
.Lx8093:
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup3
.p2align 2
eita_handler_dup3:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 96
    bnez zero, .Lx8127
    bltu s2, s7, eita_stack_underflow
.Lx8127:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup4
.p2align 2
eita_handler_dup4:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 128
    bnez zero, .Lx8161
    bltu s2, s7, eita_stack_underflow
.Lx8161:
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup5
.p2align 2
eita_handler_dup5:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 160
    bnez zero, .Lx8195
    bltu s2, s7, eita_stack_underflow
.Lx8195:
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup6
.p2align 2
eita_handler_dup6:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 192
    bnez zero, .Lx8229
    bltu s2, s7, eita_stack_underflow
.Lx8229:
    sltiu s7, s2, 192
    addi t2, s2, -192
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup7
.p2align 2
eita_handler_dup7:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 224
    bnez zero, .Lx8263
    bltu s2, s7, eita_stack_underflow
.Lx8263:
    sltiu s7, s2, 224
    addi t2, s2, -224
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup8
.p2align 2
eita_handler_dup8:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 256
    bnez zero, .Lx8297
    bltu s2, s7, eita_stack_underflow
.Lx8297:
    sltiu s7, s2, 256
    addi t2, s2, -256
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup9
.p2align 2
eita_handler_dup9:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 288
    bnez zero, .Lx8331
    bltu s2, s7, eita_stack_underflow
.Lx8331:
    sltiu s7, s2, 288
    addi t2, s2, -288
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup10
.p2align 2
eita_handler_dup10:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 320
    bnez zero, .Lx8365
    bltu s2, s7, eita_stack_underflow
.Lx8365:
    sltiu s7, s2, 320
    addi t2, s2, -320
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup11
.p2align 2
eita_handler_dup11:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 352
    bnez zero, .Lx8399
    bltu s2, s7, eita_stack_underflow
.Lx8399:
    sltiu s7, s2, 352
    addi t2, s2, -352
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup12
.p2align 2
eita_handler_dup12:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 384
    bnez zero, .Lx8433
    bltu s2, s7, eita_stack_underflow
.Lx8433:
    sltiu s7, s2, 384
    addi t2, s2, -384
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup13
.p2align 2
eita_handler_dup13:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 416
    bnez zero, .Lx8467
    bltu s2, s7, eita_stack_underflow
.Lx8467:
    sltiu s7, s2, 416
    addi t2, s2, -416
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup14
.p2align 2
eita_handler_dup14:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 448
    bnez zero, .Lx8501
    bltu s2, s7, eita_stack_underflow
.Lx8501:
    sltiu s7, s2, 448
    addi t2, s2, -448
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup15
.p2align 2
eita_handler_dup15:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 480
    bnez zero, .Lx8535
    bltu s2, s7, eita_stack_underflow
.Lx8535:
    sltiu s7, s2, 480
    addi t2, s2, -480
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_dup16
.p2align 2
eita_handler_dup16:
    li   s7, 32768
    bnez zero, eita_stack_overflow
    bgeu s2, s7, eita_stack_overflow
    li   s7, 512
    bnez zero, .Lx8569
    bltu s2, s7, eita_stack_underflow
.Lx8569:
    sltiu s7, s2, 512
    addi t2, s2, -512
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   a0, 0(t2)
    lw   a1, 4(t2)
    lw   a2, 8(t2)
    lw   a3, 12(t2)
    lw   a4, 16(t2)
    lw   a5, 20(t2)
    lw   a6, 24(t2)
    lw   a7, 28(t2)
    addi s2, s2, 32
    sltiu s7, s2, 32
    add  zero, zero, s7
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap1
.p2align 2
eita_handler_swap1:
    li   s7, 64
    bnez zero, .Lx8602
    bltu s2, s7, eita_stack_underflow
.Lx8602:
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s2, 64
    addi t2, s2, -64
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap2
.p2align 2
eita_handler_swap2:
    li   s7, 96
    bnez zero, .Lx8646
    bltu s2, s7, eita_stack_underflow
.Lx8646:
    sltiu s7, s2, 96
    addi t2, s2, -96
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap3
.p2align 2
eita_handler_swap3:
    li   s7, 128
    bnez zero, .Lx8686
    bltu s2, s7, eita_stack_underflow
.Lx8686:
    sltiu s7, s2, 128
    addi t2, s2, -128
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap4
.p2align 2
eita_handler_swap4:
    li   s7, 160
    bnez zero, .Lx8726
    bltu s2, s7, eita_stack_underflow
.Lx8726:
    sltiu s7, s2, 160
    addi t2, s2, -160
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap5
.p2align 2
eita_handler_swap5:
    li   s7, 192
    bnez zero, .Lx8766
    bltu s2, s7, eita_stack_underflow
.Lx8766:
    sltiu s7, s2, 192
    addi t2, s2, -192
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap6
.p2align 2
eita_handler_swap6:
    li   s7, 224
    bnez zero, .Lx8806
    bltu s2, s7, eita_stack_underflow
.Lx8806:
    sltiu s7, s2, 224
    addi t2, s2, -224
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap7
.p2align 2
eita_handler_swap7:
    li   s7, 256
    bnez zero, .Lx8846
    bltu s2, s7, eita_stack_underflow
.Lx8846:
    sltiu s7, s2, 256
    addi t2, s2, -256
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap8
.p2align 2
eita_handler_swap8:
    li   s7, 288
    bnez zero, .Lx8886
    bltu s2, s7, eita_stack_underflow
.Lx8886:
    sltiu s7, s2, 288
    addi t2, s2, -288
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap9
.p2align 2
eita_handler_swap9:
    li   s7, 320
    bnez zero, .Lx8926
    bltu s2, s7, eita_stack_underflow
.Lx8926:
    sltiu s7, s2, 320
    addi t2, s2, -320
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap10
.p2align 2
eita_handler_swap10:
    li   s7, 352
    bnez zero, .Lx8966
    bltu s2, s7, eita_stack_underflow
.Lx8966:
    sltiu s7, s2, 352
    addi t2, s2, -352
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap11
.p2align 2
eita_handler_swap11:
    li   s7, 384
    bnez zero, .Lx9006
    bltu s2, s7, eita_stack_underflow
.Lx9006:
    sltiu s7, s2, 384
    addi t2, s2, -384
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap12
.p2align 2
eita_handler_swap12:
    li   s7, 416
    bnez zero, .Lx9046
    bltu s2, s7, eita_stack_underflow
.Lx9046:
    sltiu s7, s2, 416
    addi t2, s2, -416
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap13
.p2align 2
eita_handler_swap13:
    li   s7, 448
    bnez zero, .Lx9086
    bltu s2, s7, eita_stack_underflow
.Lx9086:
    sltiu s7, s2, 448
    addi t2, s2, -448
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap14
.p2align 2
eita_handler_swap14:
    li   s7, 480
    bnez zero, .Lx9126
    bltu s2, s7, eita_stack_underflow
.Lx9126:
    sltiu s7, s2, 480
    addi t2, s2, -480
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap15
.p2align 2
eita_handler_swap15:
    li   s7, 512
    bnez zero, .Lx9166
    bltu s2, s7, eita_stack_underflow
.Lx9166:
    sltiu s7, s2, 512
    addi t2, s2, -512
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.text
.globl eita_handler_swap16
.p2align 2
eita_handler_swap16:
    li   s7, 544
    bnez zero, .Lx9206
    bltu s2, s7, eita_stack_underflow
.Lx9206:
    sltiu s7, s2, 544
    addi t2, s2, -544
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    lw   t0, 0(t2)
    lw   t1, 4(t2)
    lw   t4, 8(t2)
    lw   t5, 12(t2)
    lw   s8, 16(t2)
    lw   s9, 20(t2)
    lw   s10, 24(t2)
    lw   s11, 28(t2)
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    mv   a0, t0
    mv   a1, t1
    mv   a2, t4
    mv   a3, t5
    mv   a4, s8
    mv   a5, s9
    mv   a6, s10
    mv   a7, s11
    sltiu s7, s2, 32
    addi t2, s2, -32
    sub  t3, zero, s7
    add  t2, t2, s3
    sltu s7, t2, s3
    add  t3, t3, s7
    add  t3, t3, zero
    sw   a0, 0(t2)
    sw   a1, 4(t2)
    sw   a2, 8(t2)
    sw   a3, 12(t2)
    sw   a4, 16(t2)
    sw   a5, 20(t2)
    sw   a6, 24(t2)
    sw   a7, 28(t2)
    sltiu s7, s5, 3
    addi s5, s5, -3
    sw   t0, 608(s0)
    sw   t1, 612(s0)
    mv   t1, zero
    sltu t0, zero, s7
    sub  zero, zero, s7
    sltu s7, zero, t1
    sub  zero, zero, t1
    or   s7, s7, t0
    lw   t0, 608(s0)
    lw   t1, 612(s0)
    bnez s7, eita_oog
    ret
.section .note.GNU-stack,"",@progbits
