/* start.S — the smallest M-mode entry that can run the engine and report a
   fault. A misaligned access is the bug this harness exists to catch, so the
   trap vector is installed BEFORE anything else runs. */
    .section .text.init
    .globl _start
_start:
    csrw  mie, zero
    la    gp, __global_pointer$
    la    sp, __stack_top
    la    t0, _trap
    csrw  mtvec, t0
    /* zero .bss */
    la    t0, __bss_start
    la    t1, __bss_end
1:  bgeu  t0, t1, 2f
    sw    zero, 0(t0)
    addi  t0, t0, 4
    j     1b
2:  call  qemu_main
    j     _halt_ok

/* A fault's own stack. The faulting code's `sp` is not to be trusted -- a
   runaway handler is exactly the case this harness is for -- and reporting on
   it turns one fault into an endless trap loop with no output at all, which is
   what happened the first time. `_trap` is also one-shot: a second trap halts
   without touching the UART. */
    .p2align 2
    .globl _trap
_trap:
    la    t0, trap_taken
    lw    t1, 0(t0)
    bnez  t1, _halt_fail
    li    t1, 1
    sw    t1, 0(t0)
    la    sp, __trap_stack_top
    csrr  a0, mcause
    csrr  a1, mepc
    csrr  a2, mtval
    call  qemu_report_trap
    j     _halt_fail

    .section .data
    .p2align 2
trap_taken:
    .word 0
    .section .text.init

    .globl _halt_ok
_halt_ok:
    li    t0, 0x100000
    li    t1, 0x5555
    sw    t1, 0(t0)
1:  wfi
    j     1b

    .globl _halt_fail
_halt_fail:
    li    t0, 0x100000
    li    t1, 0x3333
    sw    t1, 0(t0)
1:  wfi
    j     1b
