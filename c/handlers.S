.section __TEXT,__text,regular,pure_instructions
.global _eita_run_one
.p2align 2
_eita_run_one:
    stp   x29, x30, [sp, #-96]!
    stp   x19, x20, [sp, #16]
    stp   x21, x22, [sp, #32]
    stp   x23, x24, [sp, #48]
    stp   x25, x26, [sp, #64]
    stp   x27, x28, [sp, #80]
    mov   x20, x0
    ldr   x21, [x0, #0]
    ldr   x22, [x0, #8]
    ldr   x23, [x0, #16]
    ldr   x24, [x0, #32]
    ldr   x26, [x0, #64]
    cmp   x23, #1
    b.lt  1f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
1:
    cmp   x23, #2
    b.lt  2f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
2:
    add   x21, x21, #1
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    adrp  x25, _eita_dispatch_ptr@PAGE
    ldr   x25, [x25, _eita_dispatch_ptr@PAGEOFF]
    ldr   x14, [x25, x1, lsl #3]
    br    x14

.global _eita_run
.p2align 2
_eita_run:
    stp   x29, x30, [sp, #-96]!
    stp   x19, x20, [sp, #16]
    stp   x21, x22, [sp, #32]
    stp   x23, x24, [sp, #48]
    stp   x25, x26, [sp, #64]
    stp   x27, x28, [sp, #80]
    mov   x28, sp
    mov   x20, x0
    ldr   x21, [x0, #0]
    ldr   x22, [x0, #8]
    ldr   x23, [x0, #16]
    ldr   x24, [x0, #32]
    ldr   x26, [x0, #64]
    cmp   x23, #1
    b.lt  10f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
10:
    cmp   x23, #2
    b.lt  11f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
11:
    adrp  x27, _eita_next@PAGE
    add   x27, x27, _eita_next@PAGEOFF
    adrp  x25, _eita_dispatch_ptr@PAGE
    ldr   x25, [x25, _eita_dispatch_ptr@PAGEOFF]
    ldrb  w14, [x26, x21]
    add   x21, x21, #1
    ldr   x14, [x25, x14, lsl #3]
    br    x14

.global _eita_next
.p2align 2
_eita_next:
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #112]
    cbz   x14, 1f
    stp   x29, x30, [sp, #-96]!
    stp   x6, x7, [sp, #16]
    stp   x8, x9, [sp, #32]
    stp   x10, x11, [sp, #48]
    stp   x12, x13, [sp, #64]
    mov   x0, x20
    mov   x1, x21
    mov   x2, x22
    mov   x3, x23
    ldrb  w4, [x26, x21]
    blr   x14
    ldp   x6, x7, [sp, #16]
    ldp   x8, x9, [sp, #32]
    ldp   x10, x11, [sp, #48]
    ldp   x12, x13, [sp, #64]
    ldp   x29, x30, [sp], #96
1:
    ldrb  w14, [x26, x21]
    add   x21, x21, #1
    ldr   x14, [x25, x14, lsl #3]
    br    x14

.global _eita_sync_and_ret
.p2align 2
_eita_sync_and_ret:
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    cmp   x23, #1
    b.lt  3f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
3:
    cmp   x23, #2
    b.lt  4f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
4:
    ldp   x27, x28, [sp, #80]
    ldp   x25, x26, [sp, #64]
    ldp   x23, x24, [sp, #48]
    ldp   x21, x22, [sp, #32]
    ldp   x19, x20, [sp, #16]
    ldp   x29, x30, [sp], #96
    ret

.global _eita_oog
.p2align 2
_eita_oog:
    mov   sp, x28
    mov   x22, #0
    mov   w14, #1
    strb  w14, [x20, #128]
    strb  w14, [x20, #129]
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27
.global _eita_stack_overflow
.p2align 2
_eita_stack_overflow:
    mov   sp, x28
    mov   x22, #0
    mov   w14, #1
    strb  w14, [x20, #128]
    strb  w14, [x20, #129]
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27
.global _eita_stack_underflow
.p2align 2
_eita_stack_underflow:
    mov   sp, x28
    mov   x22, #0
    mov   w14, #1
    strb  w14, [x20, #128]
    strb  w14, [x20, #129]
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27
.global _eita_static_violation
.p2align 2
_eita_static_violation:
    mov   sp, x28
    mov   x22, #0
    mov   w14, #1
    strb  w14, [x20, #128]
    strb  w14, [x20, #129]
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27

.global _eita_invalid_jump
.p2align 2
_eita_invalid_jump:
    b     _eita_oog

.global _eita_handler_add
.p2align 2
_eita_handler_add:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    adds  x10, x6, x10
    adcs  x11, x7, x11
    adcs  x12, x8, x12
    adc   x13, x9, x13
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sub
.p2align 2
_eita_handler_sub:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  x10, x6, x10
    sbcs  x11, x7, x11
    sbcs  x12, x8, x12
    sbc   x13, x9, x13
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_and
.p2align 2
_eita_handler_and:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    and   x10, x10, x6
    and   x11, x11, x7
    and   x12, x12, x8
    and   x13, x13, x9
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_or
.p2align 2
_eita_handler_or:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x10, x10, x6
    orr   x11, x11, x7
    orr   x12, x12, x8
    orr   x13, x13, x9
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_xor
.p2align 2
_eita_handler_xor:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    eor   x10, x10, x6
    eor   x11, x11, x7
    eor   x12, x12, x8
    eor   x13, x13, x9
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_lt
.p2align 2
_eita_handler_lt:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x6, x10
    sbcs  xzr, x7, x11
    sbcs  xzr, x8, x12
    sbcs  xzr, x9, x13
    cset  x6, lo
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gt
.p2align 2
_eita_handler_gt:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x10, x6
    sbcs  xzr, x11, x7
    sbcs  xzr, x12, x8
    sbcs  xzr, x13, x9
    cset  x6, lo
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_eq
.p2align 2
_eita_handler_eq:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    eor   x14, x6, x10
    eor   x15, x7, x11
    orr   x14, x14, x15
    eor   x15, x8, x12
    orr   x14, x14, x15
    eor   x15, x9, x13
    orr   x14, x14, x15
    cmp   x14, #0
    cset  x6, eq
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_iszero
.p2align 2
_eita_handler_iszero:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x6, x7
    orr   x15, x8, x9
    orr   x14, x14, x15
    cmp   x14, #0
    cset  x6, eq
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_clz
.p2align 2
_eita_handler_clz:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    clz   x0, x9
    clz   x14, x8
    clz   x15, x7
    clz   x17, x6
    add   x14, x14, #64
    add   x15, x15, #128
    add   x17, x17, #192
    cmp   x7, #0
    csel  x15, x15, x17, ne
    cmp   x8, #0
    csel  x14, x14, x15, ne
    cmp   x9, #0
    csel  x6, x0, x14, ne
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_not
.p2align 2
_eita_handler_not:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mvn   x6, x6
    mvn   x7, x7
    mvn   x8, x8
    mvn   x9, x9
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_pop
.p2align 2
_eita_handler_pop:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_stop
.p2align 2
_eita_handler_stop:
    sub   x21, x21, #1
    mov   w14, #1
    strb  w14, [x20, #128]
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27

.global _eita_handler_jumpdest
.p2align 2
_eita_handler_jumpdest:
    subs  x22, x22, #1
    b.lo  _eita_oog
    br    x27

.global _eita_handler_invalid
.p2align 2
_eita_handler_invalid:
    b     _eita_oog

.global _eita_handler_address
.p2align 2
_eita_handler_address:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #144]
    ldp   x8, x9, [x20, #160]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_origin
.p2align 2
_eita_handler_origin:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #176]
    ldp   x8, x9, [x20, #192]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_caller
.p2align 2
_eita_handler_caller:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #208]
    ldp   x8, x9, [x20, #224]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_coinbase
.p2align 2
_eita_handler_coinbase:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #336]
    ldp   x8, x9, [x20, #352]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_callvalue
.p2align 2
_eita_handler_callvalue:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #240]
    ldp   x8, x9, [x20, #256]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gasprice
.p2align 2
_eita_handler_gasprice:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #272]
    ldp   x8, x9, [x20, #288]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_chainid
.p2align 2
_eita_handler_chainid:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #304]
    ldp   x8, x9, [x20, #320]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_timestamp
.p2align 2
_eita_handler_timestamp:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #368]
    ldp   x8, x9, [x20, #384]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_number
.p2align 2
_eita_handler_number:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #400]
    ldp   x8, x9, [x20, #416]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gaslimit
.p2align 2
_eita_handler_gaslimit:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #432]
    ldp   x8, x9, [x20, #448]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_basefee
.p2align 2
_eita_handler_basefee:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #464]
    ldp   x8, x9, [x20, #480]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_prevrandao
.p2align 2
_eita_handler_prevrandao:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    add   x14, x20, #512
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_blobhash
.p2align 2
_eita_handler_blobhash:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, .Lbh_zero
    ldr   x14, [x20, #560]
    cmp   x6, x14
    b.hs  .Lbh_zero
    ldr   x15, [x20, #552]
    add   x14, x15, x6, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    b     .Lbh_done
.Lbh_zero:
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
.Lbh_done:
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_blobbasefee
.p2align 2
_eita_handler_blobbasefee:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    add   x14, x20, #568
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_pc
.p2align 2
_eita_handler_pc:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x6, x21, #1
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_msize
.p2align 2
_eita_handler_msize:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #48]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gas
.p2align 2
_eita_handler_gas:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    subs  x22, x22, #2
    b.lo  _eita_oog
    mov   x6, x22
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    br    x27

.global _eita_handler_calldatasize
.p2align 2
_eita_handler_calldatasize:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #88]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_codesize
.p2align 2
_eita_handler_codesize:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #72]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_returndatasize
.p2align 2
_eita_handler_returndatasize:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #104]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sstore
.p2align 2
_eita_handler_sstore:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    movz  x14, #2300
    cmp   x22, x14
    b.ls  _eita_oog
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x3, x24, x14, lsl #5
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #8]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #0]
    ldr   x16, [x14, #16]
    mov   x17, #104
    madd  x0, x15, x17, x16
    str   xzr, [x0, #0]
    ldp   x1, x2, [x20, #144]
    ldp   x3, x4, [x20, #160]
    stp   x1, x2, [x0, #8]
    stp   x3, x4, [x0, #24]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    stp   x6, x7, [x0, #40]
    stp   x8, x9, [x0, #56]
    stp   x10, x11, [x0, #72]
    stp   x12, x13, [x0, #88]
    ldr   x14, [x20, #504]
    add   x15, x15, #1
    str   x15, [x14, #0]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_slt
.p2align 2
_eita_handler_slt:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x6, x10
    sbcs  xzr, x7, x11
    sbcs  xzr, x8, x12
    sbcs  xzr, x9, x13
    cset  x6, lt
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sgt
.p2align 2
_eita_handler_sgt:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x10, x6
    sbcs  xzr, x11, x7
    sbcs  xzr, x12, x8
    sbcs  xzr, x13, x9
    cset  x6, lt
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_mul
.p2align 2
_eita_handler_mul:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_mul
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_div
.p2align 2
_eita_handler_div:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_div
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sdiv
.p2align 2
_eita_handler_sdiv:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_sdiv
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_mod
.p2align 2
_eita_handler_mod:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_mod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_smod
.p2align 2
_eita_handler_smod:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_smod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_exp
.p2align 2
_eita_handler_exp:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x14, #0
    cbz   x13, .Lexp_l2
    clz   x15, x13
    mov   x14, #256
    sub   x14, x14, x15
    b     .Lexp_charge
.Lexp_l2:
    cbz   x12, .Lexp_l1
    clz   x15, x12
    mov   x14, #192
    sub   x14, x14, x15
    b     .Lexp_charge
.Lexp_l1:
    cbz   x11, .Lexp_l0
    clz   x15, x11
    mov   x14, #128
    sub   x14, x14, x15
    b     .Lexp_charge
.Lexp_l0:
    cbz   x10, .Lexp_zero_e
    clz   x15, x10
    mov   x14, #64
    sub   x14, x14, x15
.Lexp_charge:
    add   x14, x14, #7
    lsr   x14, x14, #3
    b     .Lexp_do_gas
.Lexp_zero_e:
    mov   x14, #0
.Lexp_do_gas:
    mov   x15, #50
    mul   x14, x14, x15
    add   x14, x14, #10
    subs  x22, x22, x14
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_exp
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_shl
.p2align 2
_eita_handler_shl:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_shl
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_shr
.p2align 2
_eita_handler_shr:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_shr
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sar
.p2align 2
_eita_handler_sar:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_sar
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_byte
.p2align 2
_eita_handler_byte:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_byte
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_signextend
.p2align 2
_eita_handler_signextend:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_signextend
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_addmod
.p2align 2
_eita_handler_addmod:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_addmod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #8
    b.lo  _eita_oog
    br    x27

.global _eita_handler_mulmod
.p2align 2
_eita_handler_mulmod:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_mulmod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #8
    b.lo  _eita_oog
    br    x27

.global _eita_handler_calldataload
.p2align 2
_eita_handler_calldataload:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    mov   x1, x20
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_calldataload
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_calldatacopy
.p2align 2
_eita_handler_calldatacopy:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    ldp   x16, x0, [x15, #8]
    orr   x16, x16, x0
    ldr   x0, [x15, #24]
    orr   x16, x16, x0
    cbnz  x16, _eita_oog
    mov   x17, #3
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x14, 6f
    orr   x16, x7, x8
    orr   x16, x16, x9
    cbnz  x16, _eita_oog
    adds  x0, x6, x14
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_calldatacopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_codecopy
.p2align 2
_eita_handler_codecopy:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    ldp   x16, x0, [x15, #8]
    orr   x16, x16, x0
    ldr   x0, [x15, #24]
    orr   x16, x16, x0
    cbnz  x16, _eita_oog
    mov   x17, #3
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x14, 6f
    orr   x16, x7, x8
    orr   x16, x16, x9
    cbnz  x16, _eita_oog
    adds  x0, x6, x14
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_codecopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_returndatacopy
.p2align 2
_eita_handler_returndatacopy:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14, #8]
    ldr   x16, [x14, #16]
    orr   x15, x15, x16
    ldr   x16, [x14, #24]
    orr   x15, x15, x16
    cbnz  x15, _eita_oog
    ldr   x15, [x14, #0]
    adds  x15, x10, x15
    b.cs  _eita_oog
    ldr   x16, [x20, #104]
    cmp   x15, x16
    b.hi  _eita_oog
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    ldp   x16, x0, [x15, #8]
    orr   x16, x16, x0
    ldr   x0, [x15, #24]
    orr   x16, x16, x0
    cbnz  x16, _eita_oog
    mov   x17, #3
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x14, 6f
    orr   x16, x7, x8
    orr   x16, x16, x9
    cbnz  x16, _eita_oog
    adds  x0, x6, x14
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_returndatacopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_mcopy
.p2align 2
_eita_handler_mcopy:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lmcd0
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lmcd1
.Lmcd0:
    mov   x0, #0
.Lmcd1:
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lmcs0
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x14, x17, x16
    b.cs  _eita_oog
    b     .Lmcs1
.Lmcs0:
    mov   x14, #0
.Lmcs1:
    cmp   x0, x14
    csel  x0, x0, x14, hi
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    mov   x17, #3
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x0, 6f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_mcopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_keccak256
.p2align 2
_eita_handler_keccak256:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    add   x17, x10, #31
    cmp   x17, x10
    b.lo  _eita_oog
    lsr   x17, x17, #5
    add   x17, x17, x17, lsl #1
    add   x17, x17, x17
    add   x17, x17, #30
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    subs  x22, x22, x17
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    add   x3, sp, #16
    bl    _eita_helper_keccak256
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_sload
.p2align 2
_eita_handler_sload:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x14, [x20, #504]
    mov   x0, x14
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    add   x3, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #0]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_tload
.p2align 2
_eita_handler_tload:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mov   x14, #100
    subs  x22, x22, x14
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x14, [x20, #504]
    ldr   x0, [x14, #64]
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    add   x3, sp, #16
    bl    _eita_ts_tload
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_balance
.p2align 2
_eita_handler_balance:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #32]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_selfbalance
.p2align 2
_eita_handler_selfbalance:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #32]
    blr   x14
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #5
    b.lo  _eita_oog
    br    x27

.global _eita_handler_extcodesize
.p2align 2
_eita_handler_extcodesize:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #16
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #40]
    blr   x14
    mov   x14, x0
    subs  x22, x22, x14
    b.lo  _eita_oog
    ldr   x6, [sp, #16]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    ldp   x29, x30, [sp], #16
    add   sp, sp, #16
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_extcodehash
.p2align 2
_eita_handler_extcodehash:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #48]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_blockhash
.p2align 2
_eita_handler_blockhash:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #64]
    blr   x14
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #20
    b.lo  _eita_oog
    br    x27

.global _eita_handler_extcodecopy
.p2align 2
_eita_handler_extcodecopy:
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lxcd0
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lxcd1
.Lxcd0:
    mov   x0, #0
.Lxcd1:
    mov   x17, #0
    cbz   x0, 90f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
90:
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x2, x16, x15
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x3, [x14]
    ldr   x15, [x14, #8]
    ldr   x16, [x14, #16]
    orr   x15, x15, x16
    ldr   x16, [x14, #24]
    orr   x15, x15, x16
    cbz   x15, 94f
    mov   x3, #0
    sub   x3, x3, #1
94:
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x4, [x14]
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #56]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #4
    cmp   x23, #1
    b.lt  91f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
91:
    cmp   x23, #2
    b.lt  92f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
92:
    br    x27

.global _eita_handler_staticcall
.p2align 2
_eita_handler_staticcall:
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfin0_staticcall
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lcfin1_staticcall
.Lcfin0_staticcall:
    mov   x0, #0
.Lcfin1_staticcall:
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfout0_staticcall
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x14, x17, x16
    b.cs  _eita_oog
    b     .Lcfout1_staticcall
.Lcfout0_staticcall:
    mov   x14, #0
.Lcfout1_staticcall:
    cmp   x0, x14
    csel  x0, x0, x14, hi
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    sub   sp, sp, #192
    stp   x29, x30, [sp, #-16]!
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    mov   w0, #3
    str   w0, [sp, #16]
    mov   w0, #1
    str   w0, [sp, #20]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #24]
    stp   x2, x3, [sp, #40]
    stp   xzr, xzr, [sp, #56]
    stp   xzr, xzr, [sp, #72]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x15, x16, x15
    str   x15, [sp, #88]
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    str   x15, [sp, #96]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x15, x16, [x14]
    ldp   x0, x1, [x14, #16]
    orr   x16, x16, x0
    orr   x16, x16, x1
    cmp   x16, #0
    csinv x15, x15, xzr, eq
    str   x15, [sp, #104]
    stp   xzr, xzr, [sp, #112]
    stp   xzr, xzr, [sp, #128]
    ldr   x0, [x20, #504]
    add   x1, sp, #16
    add   x2, sp, #144
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #88]
    blr   x14
    ldr   x0, [sp, #152]
    str   x0, [x20, #96]
    ldr   x0, [sp, #160]
    str   x0, [x20, #104]
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldr   x1, [x14]
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldr   x2, [x14]
    mov   x0, x20
    bl    _eita_helper_returndata_to_mem
    ldr   w15, [sp, #144]
    ldr   x0, [sp, #168]
    sub   x23, x23, #5
    mov   x6, x15
    and   x6, x6, #0xff
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    cmp   x23, #2
    b.lt  L_callret_staticcall
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
L_callret_staticcall:
    ldr   x22, [x20, #8]
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    add   sp, sp, #192
    br    x27

.global _eita_handler_call
.p2align 2
_eita_handler_call:
    cmp   x23, #7
    b.lo  _eita_stack_underflow
    ldrb  w14, [x20, #130]
    cbz   w14, 93f
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14, #0]
    ldr   x16, [x14, #8]
    orr   x15, x15, x16
    ldr   x16, [x14, #16]
    orr   x15, x15, x16
    ldr   x16, [x14, #24]
    orr   x15, x15, x16
    cbnz  x15, _eita_static_violation
93:
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfin0_call
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lcfin1_call
.Lcfin0_call:
    mov   x0, #0
.Lcfin1_call:
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfout0_call
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x14, x17, x16
    b.cs  _eita_oog
    b     .Lcfout1_call
.Lcfout0_call:
    mov   x14, #0
.Lcfout1_call:
    cmp   x0, x14
    csel  x0, x0, x14, hi
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    sub   sp, sp, #192
    stp   x29, x30, [sp, #-16]!
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    mov   w0, #0
    str   w0, [sp, #16]
    mov   w0, #0
    str   w0, [sp, #20]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #24]
    stp   x2, x3, [sp, #40]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #56]
    stp   x2, x3, [sp, #72]
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x15, x16, x15
    str   x15, [sp, #88]
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    str   x15, [sp, #96]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x15, x16, [x14]
    ldp   x0, x1, [x14, #16]
    orr   x16, x16, x0
    orr   x16, x16, x1
    cmp   x16, #0
    csinv x15, x15, xzr, eq
    str   x15, [sp, #104]
    stp   xzr, xzr, [sp, #112]
    stp   xzr, xzr, [sp, #128]
    ldr   x0, [x20, #504]
    add   x1, sp, #16
    add   x2, sp, #144
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #88]
    blr   x14
    ldr   x0, [sp, #152]
    str   x0, [x20, #96]
    ldr   x0, [sp, #160]
    str   x0, [x20, #104]
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldr   x1, [x14]
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldr   x2, [x14]
    mov   x0, x20
    bl    _eita_helper_returndata_to_mem
    ldr   w15, [sp, #144]
    ldr   x0, [sp, #168]
    sub   x23, x23, #6
    mov   x6, x15
    and   x6, x6, #0xff
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    cmp   x23, #2
    b.lt  L_callret_call
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
L_callret_call:
    ldr   x22, [x20, #8]
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    add   sp, sp, #192
    br    x27

.global _eita_handler_callcode
.p2align 2
_eita_handler_callcode:
    cmp   x23, #7
    b.lo  _eita_stack_underflow
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfin0_callcode
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lcfin1_callcode
.Lcfin0_callcode:
    mov   x0, #0
.Lcfin1_callcode:
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfout0_callcode
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x14, x17, x16
    b.cs  _eita_oog
    b     .Lcfout1_callcode
.Lcfout0_callcode:
    mov   x14, #0
.Lcfout1_callcode:
    cmp   x0, x14
    csel  x0, x0, x14, hi
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    sub   sp, sp, #192
    stp   x29, x30, [sp, #-16]!
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    mov   w0, #1
    str   w0, [sp, #16]
    mov   w0, #0
    str   w0, [sp, #20]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #24]
    stp   x2, x3, [sp, #40]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #56]
    stp   x2, x3, [sp, #72]
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x15, x16, x15
    str   x15, [sp, #88]
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    str   x15, [sp, #96]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x15, x16, [x14]
    ldp   x0, x1, [x14, #16]
    orr   x16, x16, x0
    orr   x16, x16, x1
    cmp   x16, #0
    csinv x15, x15, xzr, eq
    str   x15, [sp, #104]
    stp   xzr, xzr, [sp, #112]
    stp   xzr, xzr, [sp, #128]
    ldr   x0, [x20, #504]
    add   x1, sp, #16
    add   x2, sp, #144
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #88]
    blr   x14
    ldr   x0, [sp, #152]
    str   x0, [x20, #96]
    ldr   x0, [sp, #160]
    str   x0, [x20, #104]
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldr   x1, [x14]
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldr   x2, [x14]
    mov   x0, x20
    bl    _eita_helper_returndata_to_mem
    ldr   w15, [sp, #144]
    ldr   x0, [sp, #168]
    sub   x23, x23, #6
    mov   x6, x15
    and   x6, x6, #0xff
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    cmp   x23, #2
    b.lt  L_callret_callcode
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
L_callret_callcode:
    ldr   x22, [x20, #8]
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    add   sp, sp, #192
    br    x27

.global _eita_handler_delegatecall
.p2align 2
_eita_handler_delegatecall:
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfin0_delegatecall
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lcfin1_delegatecall
.Lcfin0_delegatecall:
    mov   x0, #0
.Lcfin1_delegatecall:
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcfout0_delegatecall
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x14, x17, x16
    b.cs  _eita_oog
    b     .Lcfout1_delegatecall
.Lcfout0_delegatecall:
    mov   x14, #0
.Lcfout1_delegatecall:
    cmp   x0, x14
    csel  x0, x0, x14, hi
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    sub   sp, sp, #192
    stp   x29, x30, [sp, #-16]!
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    mov   w0, #2
    str   w0, [sp, #16]
    mov   w0, #0
    str   w0, [sp, #20]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #24]
    stp   x2, x3, [sp, #40]
    stp   xzr, xzr, [sp, #56]
    stp   xzr, xzr, [sp, #72]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x15, x16, x15
    str   x15, [sp, #88]
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    str   x15, [sp, #96]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x15, x16, [x14]
    ldp   x0, x1, [x14, #16]
    orr   x16, x16, x0
    orr   x16, x16, x1
    cmp   x16, #0
    csinv x15, x15, xzr, eq
    str   x15, [sp, #104]
    stp   xzr, xzr, [sp, #112]
    stp   xzr, xzr, [sp, #128]
    ldr   x0, [x20, #504]
    add   x1, sp, #16
    add   x2, sp, #144
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #88]
    blr   x14
    ldr   x0, [sp, #152]
    str   x0, [x20, #96]
    ldr   x0, [sp, #160]
    str   x0, [x20, #104]
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldr   x1, [x14]
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldr   x2, [x14]
    mov   x0, x20
    bl    _eita_helper_returndata_to_mem
    ldr   w15, [sp, #144]
    ldr   x0, [sp, #168]
    sub   x23, x23, #5
    mov   x6, x15
    and   x6, x6, #0xff
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    cmp   x23, #2
    b.lt  L_callret_delegatecall
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
L_callret_delegatecall:
    ldr   x22, [x20, #8]
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    add   sp, sp, #192
    br    x27

.global _eita_handler_create
.p2align 2
_eita_handler_create:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   sp, sp, #192
    stp   x29, x30, [sp, #-16]!
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcrin0_create
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lcrin1_create
.Lcrin0_create:
    mov   x0, #0
.Lcrin1_create:
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    str   x22, [x20, #8]
    mov   w0, #4
    str   w0, [sp, #16]
    str   wzr, [sp, #20]
    stp   xzr, xzr, [sp, #24]
    stp   xzr, xzr, [sp, #40]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #56]
    stp   x2, x3, [sp, #72]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x15, x16, x15
    str   x15, [sp, #88]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    str   x15, [sp, #96]
    str   x22, [sp, #104]
    stp   xzr, xzr, [sp, #112]
    stp   xzr, xzr, [sp, #128]
    ldr   x0, [x20, #504]
    add   x1, sp, #16
    add   x2, sp, #144
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #96]
    blr   x14
    ldr   x14, [sp, #152]
    str   x14, [x20, #96]
    ldr   x14, [sp, #160]
    str   x14, [x20, #104]
    ldr   w15, [sp, #144]
    cbz   w15, L_create_fail
    add   x14, sp, #176
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    b     L_create_done
L_create_fail:
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
L_create_done:
    ldr   x0, [sp, #168]
    ldr   x22, [x20, #8]
    subs  x22, x22, x0
    b.lo  _eita_oog
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    cmp   x23, #2
    b.lt  L_create_done2
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
L_create_done2:
    ldp   x29, x30, [sp], #16
    add   sp, sp, #192
    br    x27

.global _eita_handler_create2
.p2align 2
_eita_handler_create2:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   sp, sp, #192
    stp   x29, x30, [sp, #-16]!
    str   x21, [x20, #0]
    str   x22, [x20, #8]
    str   x23, [x20, #16]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lcrin0_create2
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lcrin1_create2
.Lcrin0_create2:
    mov   x0, #0
.Lcrin1_create2:
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    str   x22, [x20, #8]
    mov   w0, #5
    str   w0, [sp, #16]
    str   wzr, [sp, #20]
    stp   xzr, xzr, [sp, #24]
    stp   xzr, xzr, [sp, #40]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #56]
    stp   x2, x3, [sp, #72]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x15, x16, x15
    str   x15, [sp, #88]
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    str   x15, [sp, #96]
    str   x22, [sp, #104]
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x0, x1, [sp, #112]
    stp   x2, x3, [sp, #128]
    ldr   x0, [x20, #504]
    add   x1, sp, #16
    add   x2, sp, #144
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #96]
    blr   x14
    ldr   x14, [sp, #152]
    str   x14, [x20, #96]
    ldr   x14, [sp, #160]
    str   x14, [x20, #104]
    ldr   w15, [sp, #144]
    cbz   w15, L_create2_fail
    add   x14, sp, #176
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    b     L_create2_done
L_create2_fail:
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
L_create2_done:
    ldr   x0, [sp, #168]
    ldr   x22, [x20, #8]
    subs  x22, x22, x0
    b.lo  _eita_oog
    sub   x23, x23, #3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    cmp   x23, #2
    b.lt  L_create2_done2
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
L_create2_done2:
    ldp   x29, x30, [sp], #16
    add   sp, sp, #192
    br    x27

.global _eita_handler_selfdestruct
.p2align 2
_eita_handler_selfdestruct:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   x21, x21, #1
    mov   x14, #5000
    subs  x22, x22, x14
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, x14
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #104]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    mov   w14, #1
    strb  w14, [x20, #128]
    sub   x23, x23, #1
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27

.global _eita_handler_mload
.p2align 2
_eita_handler_mload:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, #32
    b.cs  _eita_oog
    mov   x17, #3
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #40]
    add   x15, x6, #32
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    add   x14, x14, x6
    ldr   x6, [x14, #0]
    ldr   x7, [x14, #8]
    ldr   x8, [x14, #16]
    ldr   x9, [x14, #24]
    rev   x6, x6
    rev   x7, x7
    rev   x8, x8
    rev   x9, x9
    mov   x14, x6
    mov   x6, x9
    mov   x9, x14
    mov   x14, x7
    mov   x7, x8
    mov   x8, x14
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    br    x27

.global _eita_handler_mstore
.p2align 2
_eita_handler_mstore:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, #32
    b.cs  _eita_oog
    mov   x17, #3
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
    add   x15, x6, #32
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    ldr   x14, [x20, #40]
    add   x14, x14, x6
    rev   x0, x13
    rev   x1, x12
    rev   x2, x11
    rev   x3, x10
    str   x0, [x14, #0]
    str   x1, [x14, #8]
    str   x2, [x14, #16]
    str   x3, [x14, #24]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_mstore8
.p2align 2
_eita_handler_mstore8:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, #1
    b.cs  _eita_oog
    mov   x17, #3
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #40]
    add   x15, x6, #1
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    strb  w10, [x14, x6]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_return
.p2align 2
_eita_handler_return:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   x21, x21, #1
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lror0
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lror1
.Lror0:
    mov   x0, #0
.Lror1:
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    str   x10, [x20, #120]
    ldr   x14, [x20, #40]
    add   x14, x14, x6
    str   x14, [x20, #112]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    mov   w14, #1
    strb  w14, [x20, #128]
    sub   x23, x23, #2
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27

.global _eita_handler_revert
.p2align 2
_eita_handler_revert:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   x21, x21, #1
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lrov0
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lrov1
.Lrov0:
    mov   x0, #0
.Lrov1:
    mov   x17, #0
    cbz   x0, 4f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
4:
    str   x10, [x20, #120]
    ldr   x14, [x20, #40]
    add   x14, x14, x6
    str   x14, [x20, #112]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    mov   w14, #1
    strb  w14, [x20, #128]
    strb  w14, [x20, #129]
    sub   x23, x23, #2
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27

.global _eita_handler_jump
.p2align 2
_eita_handler_jump:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_invalid_jump
    ldr   x14, [x20, #72]
    cmp   x6, x14
    b.hs  _eita_invalid_jump
    ldr   x14, [x20, #136]
    ldrb  w14, [x14, x6]
    cmp   w14, #0x1
    b.ne  _eita_invalid_jump
    mov   x21, x6
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #8
    b.lo  _eita_oog
    br    x27

.global _eita_handler_jumpi
.p2align 2
_eita_handler_jumpi:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x10, x11
    orr   x15, x12, x13
    orr   x14, x14, x15
    cbz   x14, _eita_jumpi_fallthrough
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_invalid_jump
    ldr   x14, [x20, #72]
    cmp   x6, x14
    b.hs  _eita_invalid_jump
    ldr   x14, [x20, #136]
    ldrb  w14, [x14, x6]
    cmp   w14, #0x1
    b.ne  _eita_invalid_jump
    mov   x21, x6
_eita_jumpi_pop:
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #10
    b.lo  _eita_oog
    br    x27
_eita_jumpi_fallthrough:
    b     _eita_jumpi_pop

.global _eita_handler_tstore
.p2align 2
_eita_handler_tstore:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x14, #100
    subs  x22, x22, x14
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    ldr   x1, [x20, #504]
    ldr   x0, [x1, #64]
    add   x2, x20, #144
    sub   x14, x23, #1
    add   x3, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x4, x24, x14, lsl #5
    bl    _eita_ts_tstore
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_push0
.p2align 2
_eita_handler_push0:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #2
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push1
.p2align 2
_eita_handler_push1:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #56
    add   x21, x21, #1
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push2
.p2align 2
_eita_handler_push2:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #48
    add   x21, x21, #2
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push3
.p2align 2
_eita_handler_push3:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #40
    add   x21, x21, #3
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push4
.p2align 2
_eita_handler_push4:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #32
    add   x21, x21, #4
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push5
.p2align 2
_eita_handler_push5:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #24
    add   x21, x21, #5
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push6
.p2align 2
_eita_handler_push6:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #16
    add   x21, x21, #6
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push7
.p2align 2
_eita_handler_push7:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #8
    add   x21, x21, #7
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push8
.p2align 2
_eita_handler_push8:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #8
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push9
.p2align 2
_eita_handler_push9:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #56
    add   x15, x15, #1
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #9
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push10
.p2align 2
_eita_handler_push10:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #48
    add   x15, x15, #2
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #10
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push11
.p2align 2
_eita_handler_push11:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #40
    add   x15, x15, #3
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #11
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push12
.p2align 2
_eita_handler_push12:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #32
    add   x15, x15, #4
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #12
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push13
.p2align 2
_eita_handler_push13:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #24
    add   x15, x15, #5
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #13
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push14
.p2align 2
_eita_handler_push14:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #16
    add   x15, x15, #6
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #14
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push15
.p2align 2
_eita_handler_push15:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #8
    add   x15, x15, #7
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #15
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push16
.p2align 2
_eita_handler_push16:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #16
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push17
.p2align 2
_eita_handler_push17:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #56
    add   x15, x15, #1
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #17
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push18
.p2align 2
_eita_handler_push18:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #48
    add   x15, x15, #2
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #18
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push19
.p2align 2
_eita_handler_push19:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #40
    add   x15, x15, #3
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #19
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push20
.p2align 2
_eita_handler_push20:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #32
    add   x15, x15, #4
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #20
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push21
.p2align 2
_eita_handler_push21:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #24
    add   x15, x15, #5
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #21
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push22
.p2align 2
_eita_handler_push22:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #16
    add   x15, x15, #6
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #22
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push23
.p2align 2
_eita_handler_push23:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #8
    add   x15, x15, #7
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #23
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push24
.p2align 2
_eita_handler_push24:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #24
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push25
.p2align 2
_eita_handler_push25:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #56
    add   x15, x15, #1
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #25
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push26
.p2align 2
_eita_handler_push26:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #48
    add   x15, x15, #2
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #26
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push27
.p2align 2
_eita_handler_push27:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #40
    add   x15, x15, #3
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #27
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push28
.p2align 2
_eita_handler_push28:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #32
    add   x15, x15, #4
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #28
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push29
.p2align 2
_eita_handler_push29:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #24
    add   x15, x15, #5
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #29
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push30
.p2align 2
_eita_handler_push30:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #16
    add   x15, x15, #6
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #30
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push31
.p2align 2
_eita_handler_push31:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #8
    add   x15, x15, #7
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #31
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push32
.p2align 2
_eita_handler_push32:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15, #0]
    rev   x9, x9
    ldr   x8, [x15, #8]
    rev   x8, x8
    ldr   x7, [x15, #16]
    rev   x7, x7
    ldr   x6, [x15, #24]
    rev   x6, x6
    add   x21, x21, #32
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_log0
.p2align 2
_eita_handler_log0:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #375
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #2
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #0
    add   x3, x24, x23, lsl #5
    add   x15, x23, #1
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #0
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log1
.p2align 2
_eita_handler_log1:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #750
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #3
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #1
    add   x3, x24, x23, lsl #5
    add   x15, x23, #2
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #1
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log2
.p2align 2
_eita_handler_log2:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #1125
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #4
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #2
    add   x3, x24, x23, lsl #5
    add   x15, x23, #3
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #2
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log3
.p2align 2
_eita_handler_log3:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #5
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #1500
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #5
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #3
    add   x3, x24, x23, lsl #5
    add   x15, x23, #4
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #3
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log4
.p2align 2
_eita_handler_log4:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #1875
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #6
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #4
    add   x3, x24, x23, lsl #5
    add   x15, x23, #5
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #4
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_dup1
.p2align 2
_eita_handler_dup1:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup2
.p2align 2
_eita_handler_dup2:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup3
.p2align 2
_eita_handler_dup3:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup4
.p2align 2
_eita_handler_dup4:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup5
.p2align 2
_eita_handler_dup5:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #5
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup6
.p2align 2
_eita_handler_dup6:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup7
.p2align 2
_eita_handler_dup7:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #7
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup8
.p2align 2
_eita_handler_dup8:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #8
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #8
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup9
.p2align 2
_eita_handler_dup9:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #9
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #9
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup10
.p2align 2
_eita_handler_dup10:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #10
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #10
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup11
.p2align 2
_eita_handler_dup11:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #11
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #11
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup12
.p2align 2
_eita_handler_dup12:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #12
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #12
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup13
.p2align 2
_eita_handler_dup13:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #13
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #13
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup14
.p2align 2
_eita_handler_dup14:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #14
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #14
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup15
.p2align 2
_eita_handler_dup15:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #15
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #15
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup16
.p2align 2
_eita_handler_dup16:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #16
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #16
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap1
.p2align 2
_eita_handler_swap1:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap2
.p2align 2
_eita_handler_swap2:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap3
.p2align 2
_eita_handler_swap3:
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap4
.p2align 2
_eita_handler_swap4:
    cmp   x23, #5
    b.lo  _eita_stack_underflow
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap5
.p2align 2
_eita_handler_swap5:
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap6
.p2align 2
_eita_handler_swap6:
    cmp   x23, #7
    b.lo  _eita_stack_underflow
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap7
.p2align 2
_eita_handler_swap7:
    cmp   x23, #8
    b.lo  _eita_stack_underflow
    sub   x14, x23, #8
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap8
.p2align 2
_eita_handler_swap8:
    cmp   x23, #9
    b.lo  _eita_stack_underflow
    sub   x14, x23, #9
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap9
.p2align 2
_eita_handler_swap9:
    cmp   x23, #10
    b.lo  _eita_stack_underflow
    sub   x14, x23, #10
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap10
.p2align 2
_eita_handler_swap10:
    cmp   x23, #11
    b.lo  _eita_stack_underflow
    sub   x14, x23, #11
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap11
.p2align 2
_eita_handler_swap11:
    cmp   x23, #12
    b.lo  _eita_stack_underflow
    sub   x14, x23, #12
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap12
.p2align 2
_eita_handler_swap12:
    cmp   x23, #13
    b.lo  _eita_stack_underflow
    sub   x14, x23, #13
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap13
.p2align 2
_eita_handler_swap13:
    cmp   x23, #14
    b.lo  _eita_stack_underflow
    sub   x14, x23, #14
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap14
.p2align 2
_eita_handler_swap14:
    cmp   x23, #15
    b.lo  _eita_stack_underflow
    sub   x14, x23, #15
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap15
.p2align 2
_eita_handler_swap15:
    cmp   x23, #16
    b.lo  _eita_stack_underflow
    sub   x14, x23, #16
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap16
.p2align 2
_eita_handler_swap16:
    cmp   x23, #17
    b.lo  _eita_stack_underflow
    sub   x14, x23, #17
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #3
    b.lo  _eita_oog
    br    x27

.global _eita_handler_add_f
.p2align 2
_eita_handler_add_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    adds  x10, x6, x10
    adcs  x11, x7, x11
    adcs  x12, x8, x12
    adc   x13, x9, x13
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sub_f
.p2align 2
_eita_handler_sub_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  x10, x6, x10
    sbcs  x11, x7, x11
    sbcs  x12, x8, x12
    sbc   x13, x9, x13
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_and_f
.p2align 2
_eita_handler_and_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    and   x10, x10, x6
    and   x11, x11, x7
    and   x12, x12, x8
    and   x13, x13, x9
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_or_f
.p2align 2
_eita_handler_or_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x10, x10, x6
    orr   x11, x11, x7
    orr   x12, x12, x8
    orr   x13, x13, x9
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_xor_f
.p2align 2
_eita_handler_xor_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    eor   x10, x10, x6
    eor   x11, x11, x7
    eor   x12, x12, x8
    eor   x13, x13, x9
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_lt_f
.p2align 2
_eita_handler_lt_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x6, x10
    sbcs  xzr, x7, x11
    sbcs  xzr, x8, x12
    sbcs  xzr, x9, x13
    cset  x6, lo
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gt_f
.p2align 2
_eita_handler_gt_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x10, x6
    sbcs  xzr, x11, x7
    sbcs  xzr, x12, x8
    sbcs  xzr, x13, x9
    cset  x6, lo
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_eq_f
.p2align 2
_eita_handler_eq_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    eor   x14, x6, x10
    eor   x15, x7, x11
    orr   x14, x14, x15
    eor   x15, x8, x12
    orr   x14, x14, x15
    eor   x15, x9, x13
    orr   x14, x14, x15
    cmp   x14, #0
    cset  x6, eq
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_iszero_f
.p2align 2
_eita_handler_iszero_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x6, x7
    orr   x15, x8, x9
    orr   x14, x14, x15
    cmp   x14, #0
    cset  x6, eq
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_clz_f
.p2align 2
_eita_handler_clz_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    clz   x0, x9
    clz   x14, x8
    clz   x15, x7
    clz   x17, x6
    add   x14, x14, #64
    add   x15, x15, #128
    add   x17, x17, #192
    cmp   x7, #0
    csel  x15, x15, x17, ne
    cmp   x8, #0
    csel  x14, x14, x15, ne
    cmp   x9, #0
    csel  x6, x0, x14, ne
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_not_f
.p2align 2
_eita_handler_not_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mvn   x6, x6
    mvn   x7, x7
    mvn   x8, x8
    mvn   x9, x9
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_pop_f
.p2align 2
_eita_handler_pop_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mov   x6, x10
    mov   x7, x11
    mov   x8, x12
    mov   x9, x13
    sub   x23, x23, #1
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_jumpdest_f
.p2align 2
_eita_handler_jumpdest_f:
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_address_f
.p2align 2
_eita_handler_address_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #144]
    ldp   x8, x9, [x20, #160]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_origin_f
.p2align 2
_eita_handler_origin_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #176]
    ldp   x8, x9, [x20, #192]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_caller_f
.p2align 2
_eita_handler_caller_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #208]
    ldp   x8, x9, [x20, #224]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_coinbase_f
.p2align 2
_eita_handler_coinbase_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #336]
    ldp   x8, x9, [x20, #352]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_callvalue_f
.p2align 2
_eita_handler_callvalue_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #240]
    ldp   x8, x9, [x20, #256]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gasprice_f
.p2align 2
_eita_handler_gasprice_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #272]
    ldp   x8, x9, [x20, #288]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_chainid_f
.p2align 2
_eita_handler_chainid_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #304]
    ldp   x8, x9, [x20, #320]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_timestamp_f
.p2align 2
_eita_handler_timestamp_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #368]
    ldp   x8, x9, [x20, #384]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_number_f
.p2align 2
_eita_handler_number_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #400]
    ldp   x8, x9, [x20, #416]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gaslimit_f
.p2align 2
_eita_handler_gaslimit_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #432]
    ldp   x8, x9, [x20, #448]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_basefee_f
.p2align 2
_eita_handler_basefee_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldp   x6, x7, [x20, #464]
    ldp   x8, x9, [x20, #480]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_prevrandao_f
.p2align 2
_eita_handler_prevrandao_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    add   x14, x20, #512
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_blobhash_f
.p2align 2
_eita_handler_blobhash_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, .Lbh_zero_f
    ldr   x14, [x20, #560]
    cmp   x6, x14
    b.hs  .Lbh_zero_f
    ldr   x15, [x20, #552]
    add   x14, x15, x6, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    b     .Lbh_done_f
.Lbh_zero_f:
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
.Lbh_done_f:
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_blobbasefee_f
.p2align 2
_eita_handler_blobbasefee_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    add   x14, x20, #568
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_pc_f
.p2align 2
_eita_handler_pc_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x6, x21, #1
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_msize_f
.p2align 2
_eita_handler_msize_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #48]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_gas_f
.p2align 2
_eita_handler_gas_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    subs  x22, x22, #0
    b.lo  _eita_oog
    mov   x6, x22
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    br    x27

.global _eita_handler_calldatasize_f
.p2align 2
_eita_handler_calldatasize_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #88]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_codesize_f
.p2align 2
_eita_handler_codesize_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #72]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_returndatasize_f
.p2align 2
_eita_handler_returndatasize_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    ldr   x6, [x20, #104]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sstore_f
.p2align 2
_eita_handler_sstore_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    movz  x14, #2300
    cmp   x22, x14
    b.ls  _eita_oog
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x3, x24, x14, lsl #5
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #8]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #0]
    ldr   x16, [x14, #16]
    mov   x17, #104
    madd  x0, x15, x17, x16
    str   xzr, [x0, #0]
    ldp   x1, x2, [x20, #144]
    ldp   x3, x4, [x20, #160]
    stp   x1, x2, [x0, #8]
    stp   x3, x4, [x0, #24]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    stp   x6, x7, [x0, #40]
    stp   x8, x9, [x0, #56]
    stp   x10, x11, [x0, #72]
    stp   x12, x13, [x0, #88]
    ldr   x14, [x20, #504]
    add   x15, x15, #1
    str   x15, [x14, #0]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_slt_f
.p2align 2
_eita_handler_slt_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x6, x10
    sbcs  xzr, x7, x11
    sbcs  xzr, x8, x12
    sbcs  xzr, x9, x13
    cset  x6, lt
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sgt_f
.p2align 2
_eita_handler_sgt_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    subs  xzr, x10, x6
    sbcs  xzr, x11, x7
    sbcs  xzr, x12, x8
    sbcs  xzr, x13, x9
    cset  x6, lt
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_mul_f
.p2align 2
_eita_handler_mul_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_mul
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_div_f
.p2align 2
_eita_handler_div_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_div
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sdiv_f
.p2align 2
_eita_handler_sdiv_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_sdiv
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_mod_f
.p2align 2
_eita_handler_mod_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_mod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_smod_f
.p2align 2
_eita_handler_smod_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_smod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_exp_f
.p2align 2
_eita_handler_exp_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x14, #0
    cbz   x13, .Lexp_l2_f
    clz   x15, x13
    mov   x14, #256
    sub   x14, x14, x15
    b     .Lexp_charge_f
.Lexp_l2_f:
    cbz   x12, .Lexp_l1_f
    clz   x15, x12
    mov   x14, #192
    sub   x14, x14, x15
    b     .Lexp_charge_f
.Lexp_l1_f:
    cbz   x11, .Lexp_l0_f
    clz   x15, x11
    mov   x14, #128
    sub   x14, x14, x15
    b     .Lexp_charge_f
.Lexp_l0_f:
    cbz   x10, .Lexp_zero_e_f
    clz   x15, x10
    mov   x14, #64
    sub   x14, x14, x15
.Lexp_charge_f:
    add   x14, x14, #7
    lsr   x14, x14, #3
    b     .Lexp_do_gas_f
.Lexp_zero_e_f:
    mov   x14, #0
.Lexp_do_gas_f:
    mov   x15, #50
    mul   x14, x14, x15
    add   x14, x14, #0
    subs  x22, x22, x14
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_exp
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_shl_f
.p2align 2
_eita_handler_shl_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_shl
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_shr_f
.p2align 2
_eita_handler_shr_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_shr
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sar_f
.p2align 2
_eita_handler_sar_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_sar
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_byte_f
.p2align 2
_eita_handler_byte_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_byte
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_signextend_f
.p2align 2
_eita_handler_signextend_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_signextend
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_addmod_f
.p2align 2
_eita_handler_addmod_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_addmod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_mulmod_f
.p2align 2
_eita_handler_mulmod_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_mulmod
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_calldataload_f
.p2align 2
_eita_handler_calldataload_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    mov   x1, x20
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_calldataload
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_calldatacopy_f
.p2align 2
_eita_handler_calldatacopy_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    ldp   x16, x0, [x15, #8]
    orr   x16, x16, x0
    ldr   x0, [x15, #24]
    orr   x16, x16, x0
    cbnz  x16, _eita_oog
    mov   x17, #0
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x14, 6f
    orr   x16, x7, x8
    orr   x16, x16, x9
    cbnz  x16, _eita_oog
    adds  x0, x6, x14
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_calldatacopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_codecopy_f
.p2align 2
_eita_handler_codecopy_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    ldp   x16, x0, [x15, #8]
    orr   x16, x16, x0
    ldr   x0, [x15, #24]
    orr   x16, x16, x0
    cbnz  x16, _eita_oog
    mov   x17, #0
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x14, 6f
    orr   x16, x7, x8
    orr   x16, x16, x9
    cbnz  x16, _eita_oog
    adds  x0, x6, x14
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_codecopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_returndatacopy_f
.p2align 2
_eita_handler_returndatacopy_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14, #8]
    ldr   x16, [x14, #16]
    orr   x15, x15, x16
    ldr   x16, [x14, #24]
    orr   x15, x15, x16
    cbnz  x15, _eita_oog
    ldr   x15, [x14, #0]
    adds  x15, x10, x15
    b.cs  _eita_oog
    ldr   x16, [x20, #104]
    cmp   x15, x16
    b.hi  _eita_oog
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    ldp   x16, x0, [x15, #8]
    orr   x16, x16, x0
    ldr   x0, [x15, #24]
    orr   x16, x16, x0
    cbnz  x16, _eita_oog
    mov   x17, #0
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x14, 6f
    orr   x16, x7, x8
    orr   x16, x16, x9
    cbnz  x16, _eita_oog
    adds  x0, x6, x14
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_returndatacopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_mcopy_f
.p2align 2
_eita_handler_mcopy_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lmcd0_f
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lmcd1_f
.Lmcd0_f:
    mov   x0, #0
.Lmcd1_f:
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lmcs0_f
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x14, x17, x16
    b.cs  _eita_oog
    b     .Lmcs1_f
.Lmcs0_f:
    mov   x14, #0
.Lmcs1_f:
    cmp   x0, x14
    csel  x0, x0, x14, hi
    sub   x14, x23, #3
    add   x15, x24, x14, lsl #5
    ldr   x14, [x15]
    mov   x17, #0
    add   x16, x14, #31
    cmp   x16, x14
    b.lo  _eita_oog
    lsr   x16, x16, #5
    add   x16, x16, x16, lsl #1
    add   x17, x17, x16
    cbz   x0, 6f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
6:
    subs  x22, x22, x17
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #3
    add   x3, x24, x14, lsl #5
    bl    _eita_helper_mcopy
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #3
    cmp   x23, #1
    b.lt  7f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
7:
    cmp   x23, #2
    b.lt  8f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
8:
    br    x27

.global _eita_handler_keccak256_f
.p2align 2
_eita_handler_keccak256_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    add   x17, x10, #31
    cmp   x17, x10
    b.lo  _eita_oog
    lsr   x17, x17, #5
    add   x17, x17, x17, lsl #1
    add   x17, x17, x17
    add   x17, x17, #0
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    subs  x22, x22, x17
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    mov   x0, x20
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    add   x3, sp, #16
    bl    _eita_helper_keccak256
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_sload_f
.p2align 2
_eita_handler_sload_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x14, [x20, #504]
    mov   x0, x14
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    add   x3, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #0]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_tload_f
.p2align 2
_eita_handler_tload_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mov   x14, #100
    subs  x22, x22, x14
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x14, [x20, #504]
    ldr   x0, [x14, #64]
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    add   x3, sp, #16
    bl    _eita_ts_tload
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_balance_f
.p2align 2
_eita_handler_balance_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #32]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_selfbalance_f
.p2align 2
_eita_handler_selfbalance_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #32]
    blr   x14
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_extcodesize_f
.p2align 2
_eita_handler_extcodesize_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #16
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #40]
    blr   x14
    mov   x14, x0
    subs  x22, x22, x14
    b.lo  _eita_oog
    ldr   x6, [sp, #16]
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    ldp   x29, x30, [sp], #16
    add   sp, sp, #16
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_extcodehash_f
.p2align 2
_eita_handler_extcodehash_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #48]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_blockhash_f
.p2align 2
_eita_handler_blockhash_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    add   x2, sp, #16
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #64]
    blr   x14
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_extcodecopy_f
.p2align 2
_eita_handler_extcodecopy_f:
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x16, [x14, #0]
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    cbz   x16, .Lxcd0_f
    ldr   x15, [x14, #8]
    ldr   x17, [x14, #16]
    orr   x15, x15, x17
    ldr   x17, [x14, #24]
    orr   x15, x15, x17
    cbnz  x15, _eita_oog
    ldr   x17, [x14, #0]
    adds  x0, x17, x16
    b.cs  _eita_oog
    b     .Lxcd1_f
.Lxcd0_f:
    mov   x0, #0
.Lxcd1_f:
    mov   x17, #0
    cbz   x0, 90f
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
90:
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldr   x15, [x14]
    ldr   x16, [x20, #40]
    add   x2, x16, x15
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldr   x3, [x14]
    ldr   x15, [x14, #8]
    ldr   x16, [x14, #16]
    orr   x15, x15, x16
    ldr   x16, [x14, #24]
    orr   x15, x15, x16
    cbz   x15, 94f
    mov   x3, #0
    sub   x3, x3, #1
94:
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldr   x4, [x14]
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #56]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #4
    cmp   x23, #1
    b.lt  91f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
91:
    cmp   x23, #2
    b.lt  92f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
92:
    br    x27

.global _eita_handler_mload_f
.p2align 2
_eita_handler_mload_f:
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, #32
    b.cs  _eita_oog
    mov   x17, #0
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #40]
    add   x15, x6, #32
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    add   x14, x14, x6
    ldr   x6, [x14, #0]
    ldr   x7, [x14, #8]
    ldr   x8, [x14, #16]
    ldr   x9, [x14, #24]
    rev   x6, x6
    rev   x7, x7
    rev   x8, x8
    rev   x9, x9
    mov   x14, x6
    mov   x6, x9
    mov   x9, x14
    mov   x14, x7
    mov   x7, x8
    mov   x8, x14
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    br    x27

.global _eita_handler_mstore_f
.p2align 2
_eita_handler_mstore_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, #32
    b.cs  _eita_oog
    mov   x17, #0
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
    add   x15, x6, #32
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    ldr   x14, [x20, #40]
    add   x14, x14, x6
    rev   x0, x13
    rev   x1, x12
    rev   x2, x11
    rev   x3, x10
    str   x0, [x14, #0]
    str   x1, [x14, #8]
    str   x2, [x14, #16]
    str   x3, [x14, #24]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_mstore8_f
.p2align 2
_eita_handler_mstore8_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, #1
    b.cs  _eita_oog
    mov   x17, #0
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #40]
    add   x15, x6, #1
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    strb  w10, [x14, x6]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_tstore_f
.p2align 2
_eita_handler_tstore_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x14, #100
    subs  x22, x22, x14
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    ldr   x1, [x20, #504]
    ldr   x0, [x1, #64]
    add   x2, x20, #144
    sub   x14, x23, #1
    add   x3, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x4, x24, x14, lsl #5
    bl    _eita_ts_tstore
    ldp   x29, x30, [sp], #16
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_push0_f
.p2align 2
_eita_handler_push0_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push1_f
.p2align 2
_eita_handler_push1_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #56
    add   x21, x21, #1
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push2_f
.p2align 2
_eita_handler_push2_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #48
    add   x21, x21, #2
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push3_f
.p2align 2
_eita_handler_push3_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #40
    add   x21, x21, #3
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push4_f
.p2align 2
_eita_handler_push4_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #32
    add   x21, x21, #4
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push5_f
.p2align 2
_eita_handler_push5_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #24
    add   x21, x21, #5
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push6_f
.p2align 2
_eita_handler_push6_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #16
    add   x21, x21, #6
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push7_f
.p2align 2
_eita_handler_push7_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15]
    rev   x6, x6
    lsr   x6, x6, #8
    add   x21, x21, #7
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push8_f
.p2align 2
_eita_handler_push8_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #8
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push9_f
.p2align 2
_eita_handler_push9_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #56
    add   x15, x15, #1
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #9
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push10_f
.p2align 2
_eita_handler_push10_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #48
    add   x15, x15, #2
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #10
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push11_f
.p2align 2
_eita_handler_push11_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #40
    add   x15, x15, #3
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #11
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push12_f
.p2align 2
_eita_handler_push12_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #32
    add   x15, x15, #4
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #12
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push13_f
.p2align 2
_eita_handler_push13_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #24
    add   x15, x15, #5
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #13
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push14_f
.p2align 2
_eita_handler_push14_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #16
    add   x15, x15, #6
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #14
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push15_f
.p2align 2
_eita_handler_push15_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15]
    rev   x7, x7
    lsr   x7, x7, #8
    add   x15, x15, #7
    ldr   x6, [x15, #0]
    rev   x6, x6
    add   x21, x21, #15
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push16_f
.p2align 2
_eita_handler_push16_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #16
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push17_f
.p2align 2
_eita_handler_push17_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #56
    add   x15, x15, #1
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #17
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push18_f
.p2align 2
_eita_handler_push18_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #48
    add   x15, x15, #2
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #18
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push19_f
.p2align 2
_eita_handler_push19_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #40
    add   x15, x15, #3
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #19
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push20_f
.p2align 2
_eita_handler_push20_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #32
    add   x15, x15, #4
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #20
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push21_f
.p2align 2
_eita_handler_push21_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #24
    add   x15, x15, #5
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #21
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push22_f
.p2align 2
_eita_handler_push22_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #16
    add   x15, x15, #6
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #22
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push23_f
.p2align 2
_eita_handler_push23_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15]
    rev   x8, x8
    lsr   x8, x8, #8
    add   x15, x15, #7
    ldr   x7, [x15, #0]
    rev   x7, x7
    ldr   x6, [x15, #8]
    rev   x6, x6
    add   x21, x21, #23
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push24_f
.p2align 2
_eita_handler_push24_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #24
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push25_f
.p2align 2
_eita_handler_push25_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #56
    add   x15, x15, #1
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #25
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push26_f
.p2align 2
_eita_handler_push26_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #48
    add   x15, x15, #2
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #26
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push27_f
.p2align 2
_eita_handler_push27_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #40
    add   x15, x15, #3
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #27
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push28_f
.p2align 2
_eita_handler_push28_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #32
    add   x15, x15, #4
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #28
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push29_f
.p2align 2
_eita_handler_push29_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #24
    add   x15, x15, #5
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #29
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push30_f
.p2align 2
_eita_handler_push30_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #16
    add   x15, x15, #6
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #30
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push31_f
.p2align 2
_eita_handler_push31_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15]
    rev   x9, x9
    lsr   x9, x9, #8
    add   x15, x15, #7
    ldr   x8, [x15, #0]
    rev   x8, x8
    ldr   x7, [x15, #8]
    rev   x7, x7
    ldr   x6, [x15, #16]
    rev   x6, x6
    add   x21, x21, #31
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_push32_f
.p2align 2
_eita_handler_push32_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    mov   x6, #0
    mov   x7, #0
    mov   x8, #0
    mov   x9, #0
    add   x15, x26, x21
    ldr   x9, [x15, #0]
    rev   x9, x9
    ldr   x8, [x15, #8]
    rev   x8, x8
    ldr   x7, [x15, #16]
    rev   x7, x7
    ldr   x6, [x15, #24]
    rev   x6, x6
    add   x21, x21, #32
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_log0_f
.p2align 2
_eita_handler_log0_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #0
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #2
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #0
    add   x3, x24, x23, lsl #5
    add   x15, x23, #1
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #0
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log1_f
.p2align 2
_eita_handler_log1_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #0
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #3
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #1
    add   x3, x24, x23, lsl #5
    add   x15, x23, #2
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #1
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log2_f
.p2align 2
_eita_handler_log2_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #0
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #4
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #2
    add   x3, x24, x23, lsl #5
    add   x15, x23, #3
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #2
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log3_f
.p2align 2
_eita_handler_log3_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #5
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #0
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #5
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #3
    add   x3, x24, x23, lsl #5
    add   x15, x23, #4
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #3
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_log4_f
.p2align 2
_eita_handler_log4_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    orr   x14, x11, x12
    orr   x14, x14, x13
    cbnz  x14, _eita_oog
    mov   x17, #0
    add   x17, x17, x10, lsl #3
    cbz   x10, 4f
    orr   x14, x7, x8
    orr   x14, x14, x9
    cbnz  x14, _eita_oog
    adds  x0, x6, x10
    b.cs  _eita_oog
    ldr   x14, [x20, #56]
    cmp   x0, x14
    b.hi  _eita_oog
    add   x14, x0, #31
    lsr   x14, x14, #5
    ldr   x15, [x20, #48]
    lsr   x15, x15, #5
    cmp   x14, x15
    b.ls  7f
    mul   x16, x14, x14
    add   x16, x14, x16, lsr #9
    add   x16, x16, x14, lsl #1
    mul   x14, x15, x15
    add   x14, x15, x14, lsr #9
    add   x14, x14, x15, lsl #1
    sub   x16, x16, x14
    add   x17, x17, x16
    add   x14, x0, #31
    lsr   x14, x14, #5
    lsl   x14, x14, #5
    str   x14, [x20, #48]
7:
4:
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #8]
    add   x15, x15, #1
    str   x15, [x14, #8]
    add   x15, x6, x10
    ldr   x16, [x20, #24]
    cmp   x15, x16
    csel  x16, x15, x16, hi
    str   x16, [x20, #24]
    sub   x23, x23, #6
    subs  x22, x22, x17
    b.lo  _eita_oog
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #72]
    cbz   x14, 7f
    stp   x29, x30, [sp, #-16]!
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, #4
    add   x3, x24, x23, lsl #5
    add   x15, x23, #5
    add   x15, x24, x15, lsl #5
    ldr   x15, [x15]
    ldr   x4, [x20, #40]
    add   x4, x4, x15
    add   x15, x23, #4
    add   x15, x24, x15, lsl #5
    ldr   x5, [x15]
    blr   x14
    ldp   x29, x30, [sp], #16
7:
    cmp   x23, #1
    b.lt  5f
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
5:
    cmp   x23, #2
    b.lt  6f
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
6:
    br    x27

.global _eita_handler_dup1_f
.p2align 2
_eita_handler_dup1_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup2_f
.p2align 2
_eita_handler_dup2_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup3_f
.p2align 2
_eita_handler_dup3_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup4_f
.p2align 2
_eita_handler_dup4_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup5_f
.p2align 2
_eita_handler_dup5_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #5
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup6_f
.p2align 2
_eita_handler_dup6_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup7_f
.p2align 2
_eita_handler_dup7_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #7
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup8_f
.p2align 2
_eita_handler_dup8_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #8
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #8
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup9_f
.p2align 2
_eita_handler_dup9_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #9
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #9
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup10_f
.p2align 2
_eita_handler_dup10_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #10
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #10
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup11_f
.p2align 2
_eita_handler_dup11_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #11
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #11
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup12_f
.p2align 2
_eita_handler_dup12_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #12
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #12
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup13_f
.p2align 2
_eita_handler_dup13_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #13
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #13
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup14_f
.p2align 2
_eita_handler_dup14_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #14
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #14
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup15_f
.p2align 2
_eita_handler_dup15_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #15
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #15
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_dup16_f
.p2align 2
_eita_handler_dup16_f:
    cmp   x23, #1024
    b.hs  _eita_stack_overflow
    cmp   x23, #16
    b.lo  _eita_stack_underflow
    mov   x10, x6
    mov   x11, x7
    mov   x12, x8
    mov   x13, x9
    sub   x14, x23, #16
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    add   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap1_f
.p2align 2
_eita_handler_swap1_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap2_f
.p2align 2
_eita_handler_swap2_f:
    cmp   x23, #3
    b.lo  _eita_stack_underflow
    sub   x14, x23, #3
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap3_f
.p2align 2
_eita_handler_swap3_f:
    cmp   x23, #4
    b.lo  _eita_stack_underflow
    sub   x14, x23, #4
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap4_f
.p2align 2
_eita_handler_swap4_f:
    cmp   x23, #5
    b.lo  _eita_stack_underflow
    sub   x14, x23, #5
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap5_f
.p2align 2
_eita_handler_swap5_f:
    cmp   x23, #6
    b.lo  _eita_stack_underflow
    sub   x14, x23, #6
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap6_f
.p2align 2
_eita_handler_swap6_f:
    cmp   x23, #7
    b.lo  _eita_stack_underflow
    sub   x14, x23, #7
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap7_f
.p2align 2
_eita_handler_swap7_f:
    cmp   x23, #8
    b.lo  _eita_stack_underflow
    sub   x14, x23, #8
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap8_f
.p2align 2
_eita_handler_swap8_f:
    cmp   x23, #9
    b.lo  _eita_stack_underflow
    sub   x14, x23, #9
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap9_f
.p2align 2
_eita_handler_swap9_f:
    cmp   x23, #10
    b.lo  _eita_stack_underflow
    sub   x14, x23, #10
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap10_f
.p2align 2
_eita_handler_swap10_f:
    cmp   x23, #11
    b.lo  _eita_stack_underflow
    sub   x14, x23, #11
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap11_f
.p2align 2
_eita_handler_swap11_f:
    cmp   x23, #12
    b.lo  _eita_stack_underflow
    sub   x14, x23, #12
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap12_f
.p2align 2
_eita_handler_swap12_f:
    cmp   x23, #13
    b.lo  _eita_stack_underflow
    sub   x14, x23, #13
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap13_f
.p2align 2
_eita_handler_swap13_f:
    cmp   x23, #14
    b.lo  _eita_stack_underflow
    sub   x14, x23, #14
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap14_f
.p2align 2
_eita_handler_swap14_f:
    cmp   x23, #15
    b.lo  _eita_stack_underflow
    sub   x14, x23, #15
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap15_f
.p2align 2
_eita_handler_swap15_f:
    cmp   x23, #16
    b.lo  _eita_stack_underflow
    sub   x14, x23, #16
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_swap16_f
.p2align 2
_eita_handler_swap16_f:
    cmp   x23, #17
    b.lo  _eita_stack_underflow
    sub   x14, x23, #17
    add   x14, x24, x14, lsl #5
    ldp   x0, x1, [x14]
    ldp   x2, x3, [x14, #16]
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    mov   x6, x0
    mov   x7, x1
    mov   x8, x2
    mov   x9, x3
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    subs  x22, x22, #0
    b.lo  _eita_oog
    br    x27

.global _eita_handler_sstore_nosentry_f
.p2align 2
_eita_handler_sstore_nosentry_f:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x3, x24, x14, lsl #5
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #8]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #0]
    ldr   x16, [x14, #16]
    mov   x17, #104
    madd  x0, x15, x17, x16
    str   xzr, [x0, #0]
    ldp   x1, x2, [x20, #144]
    ldp   x3, x4, [x20, #160]
    stp   x1, x2, [x0, #8]
    stp   x3, x4, [x0, #24]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    stp   x6, x7, [x0, #40]
    stp   x8, x9, [x0, #56]
    stp   x10, x11, [x0, #72]
    stp   x12, x13, [x0, #88]
    ldr   x14, [x20, #504]
    add   x15, x15, #1
    str   x15, [x14, #0]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_exp_pre160_f
.p2align 2
_eita_handler_exp_pre160_f:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x14, #0
    cbz   x13, .Lexp_l2_pre160_f
    clz   x15, x13
    mov   x14, #256
    sub   x14, x14, x15
    b     .Lexp_charge_pre160_f
.Lexp_l2_pre160_f:
    cbz   x12, .Lexp_l1_pre160_f
    clz   x15, x12
    mov   x14, #192
    sub   x14, x14, x15
    b     .Lexp_charge_pre160_f
.Lexp_l1_pre160_f:
    cbz   x11, .Lexp_l0_pre160_f
    clz   x15, x11
    mov   x14, #128
    sub   x14, x14, x15
    b     .Lexp_charge_pre160_f
.Lexp_l0_pre160_f:
    cbz   x10, .Lexp_zero_e_pre160_f
    clz   x15, x10
    mov   x14, #64
    sub   x14, x14, x15
.Lexp_charge_pre160_f:
    add   x14, x14, #7
    lsr   x14, x14, #3
    b     .Lexp_do_gas_pre160_f
.Lexp_zero_e_pre160_f:
    mov   x14, #0
.Lexp_do_gas_pre160_f:
    mov   x15, #10
    mul   x14, x14, x15
    add   x14, x14, #0
    subs  x22, x22, x14
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_exp
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_exp_pre160
.p2align 2
_eita_handler_exp_pre160:
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    mov   x14, #0
    cbz   x13, .Lexp_l2_pre160
    clz   x15, x13
    mov   x14, #256
    sub   x14, x14, x15
    b     .Lexp_charge_pre160
.Lexp_l2_pre160:
    cbz   x12, .Lexp_l1_pre160
    clz   x15, x12
    mov   x14, #192
    sub   x14, x14, x15
    b     .Lexp_charge_pre160
.Lexp_l1_pre160:
    cbz   x11, .Lexp_l0_pre160
    clz   x15, x11
    mov   x14, #128
    sub   x14, x14, x15
    b     .Lexp_charge_pre160
.Lexp_l0_pre160:
    cbz   x10, .Lexp_zero_e_pre160
    clz   x15, x10
    mov   x14, #64
    sub   x14, x14, x15
.Lexp_charge_pre160:
    add   x14, x14, #7
    lsr   x14, x14, #3
    b     .Lexp_do_gas_pre160
.Lexp_zero_e_pre160:
    mov   x14, #0
.Lexp_do_gas_pre160:
    mov   x15, #10
    mul   x14, x14, x15
    add   x14, x14, #10
    subs  x22, x22, x14
    b.lo  _eita_oog
    sub   sp, sp, #32
    stp   x29, x30, [sp, #-16]!
    add   x0, sp, #16
    sub   x14, x23, #1
    add   x1, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x2, x24, x14, lsl #5
    bl    _eita_helper_exp
    add   x14, sp, #16
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    ldp   x29, x30, [sp], #16
    add   sp, sp, #32
    sub   x23, x23, #1
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.global _eita_handler_selfdestruct_pre150
.p2align 2
_eita_handler_selfdestruct_pre150:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #1
    b.lo  _eita_stack_underflow
    sub   x21, x21, #1
    mov   x14, #0
    subs  x22, x22, x14
    b.lo  _eita_oog
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    mov   x2, x14
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #104]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    mov   w14, #1
    strb  w14, [x20, #128]
    sub   x23, x23, #1
    adrp  x27, _eita_sync_and_ret@PAGE
    add   x27, x27, _eita_sync_and_ret@PAGEOFF
    br    x27

.global _eita_handler_sstore_nosentry
.p2align 2
_eita_handler_sstore_nosentry:
    ldrb  w14, [x20, #130]
    cbnz  w14, _eita_static_violation
    cmp   x23, #2
    b.lo  _eita_stack_underflow
    stp   x29, x30, [sp, #-16]!
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    stp   x6, x7, [x14]
    stp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    stp   x10, x11, [x14]
    stp   x12, x13, [x14, #16]
    ldr   x0, [x20, #504]
    add   x1, x20, #144
    sub   x14, x23, #1
    add   x2, x24, x14, lsl #5
    sub   x14, x23, #2
    add   x3, x24, x14, lsl #5
    ldr   x14, [x20, #496]
    ldr   x14, [x14, #8]
    blr   x14
    subs  x22, x22, x0
    b.lo  _eita_oog
    ldp   x29, x30, [sp], #16
    ldr   x14, [x20, #504]
    ldr   x15, [x14, #0]
    ldr   x16, [x14, #16]
    mov   x17, #104
    madd  x0, x15, x17, x16
    str   xzr, [x0, #0]
    ldp   x1, x2, [x20, #144]
    ldp   x3, x4, [x20, #160]
    stp   x1, x2, [x0, #8]
    stp   x3, x4, [x0, #24]
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    stp   x6, x7, [x0, #40]
    stp   x8, x9, [x0, #56]
    stp   x10, x11, [x0, #72]
    stp   x12, x13, [x0, #88]
    ldr   x14, [x20, #504]
    add   x15, x15, #1
    str   x15, [x14, #0]
    sub   x23, x23, #2
    sub   x14, x23, #1
    add   x14, x24, x14, lsl #5
    ldp   x6, x7, [x14]
    ldp   x8, x9, [x14, #16]
    sub   x14, x23, #2
    add   x14, x24, x14, lsl #5
    ldp   x10, x11, [x14]
    ldp   x12, x13, [x14, #16]
    br    x27

.data
.global _eita_dispatch_table
.p2align 3
_eita_dispatch_table:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_blobhash
    .quad   _eita_handler_blobbasefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_tload
    .quad   _eita_handler_tstore
    .quad   _eita_handler_mcopy
    .quad   _eita_handler_push0
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.global _eita_dispatch_ptr
.p2align 3
_eita_dispatch_ptr:
    .quad   _eita_dispatch_table

.data
.global _eita_dispatch_table_frontier
.p2align 3
_eita_dispatch_table_frontier:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp_pre160
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct_pre150
.data
.global _eita_dispatch_table_homestead
.p2align 3
_eita_dispatch_table_homestead:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp_pre160
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct_pre150
.data
.global _eita_dispatch_table_dao_fork
.p2align 3
_eita_dispatch_table_dao_fork:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp_pre160
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct_pre150
.data
.global _eita_dispatch_table_tangerine_whistle
.p2align 3
_eita_dispatch_table_tangerine_whistle:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp_pre160
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_spurious_dragon
.p2align 3
_eita_dispatch_table_spurious_dragon:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_byzantium
.p2align 3
_eita_dispatch_table_byzantium:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_invalid
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_constantinople
.p2align 3
_eita_dispatch_table_constantinople:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_petersburg
.p2align 3
_eita_dispatch_table_petersburg:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore_nosentry
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_istanbul
.p2align 3
_eita_dispatch_table_istanbul:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_muir_glacier
.p2align 3
_eita_dispatch_table_muir_glacier:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_berlin
.p2align 3
_eita_dispatch_table_berlin:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_london
.p2align 3
_eita_dispatch_table_london:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_arrow_glacier
.p2align 3
_eita_dispatch_table_arrow_glacier:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_gray_glacier
.p2align 3
_eita_dispatch_table_gray_glacier:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_paris
.p2align 3
_eita_dispatch_table_paris:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_shanghai
.p2align 3
_eita_dispatch_table_shanghai:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_push0
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_dispatch_table_osaka
.p2align 3
_eita_dispatch_table_osaka:
    .quad   _eita_handler_stop
    .quad   _eita_handler_add
    .quad   _eita_handler_mul
    .quad   _eita_handler_sub
    .quad   _eita_handler_div
    .quad   _eita_handler_sdiv
    .quad   _eita_handler_mod
    .quad   _eita_handler_smod
    .quad   _eita_handler_addmod
    .quad   _eita_handler_mulmod
    .quad   _eita_handler_exp
    .quad   _eita_handler_signextend
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_lt
    .quad   _eita_handler_gt
    .quad   _eita_handler_slt
    .quad   _eita_handler_sgt
    .quad   _eita_handler_eq
    .quad   _eita_handler_iszero
    .quad   _eita_handler_and
    .quad   _eita_handler_or
    .quad   _eita_handler_xor
    .quad   _eita_handler_not
    .quad   _eita_handler_byte
    .quad   _eita_handler_shl
    .quad   _eita_handler_shr
    .quad   _eita_handler_sar
    .quad   _eita_handler_clz
    .quad   _eita_handler_invalid
    .quad   _eita_handler_keccak256
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_address
    .quad   _eita_handler_balance
    .quad   _eita_handler_origin
    .quad   _eita_handler_caller
    .quad   _eita_handler_callvalue
    .quad   _eita_handler_calldataload
    .quad   _eita_handler_calldatasize
    .quad   _eita_handler_calldatacopy
    .quad   _eita_handler_codesize
    .quad   _eita_handler_codecopy
    .quad   _eita_handler_gasprice
    .quad   _eita_handler_extcodesize
    .quad   _eita_handler_extcodecopy
    .quad   _eita_handler_returndatasize
    .quad   _eita_handler_returndatacopy
    .quad   _eita_handler_extcodehash
    .quad   _eita_handler_blockhash
    .quad   _eita_handler_coinbase
    .quad   _eita_handler_timestamp
    .quad   _eita_handler_number
    .quad   _eita_handler_prevrandao
    .quad   _eita_handler_gaslimit
    .quad   _eita_handler_chainid
    .quad   _eita_handler_selfbalance
    .quad   _eita_handler_basefee
    .quad   _eita_handler_blobhash
    .quad   _eita_handler_blobbasefee
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_pop
    .quad   _eita_handler_mload
    .quad   _eita_handler_mstore
    .quad   _eita_handler_mstore8
    .quad   _eita_handler_sload
    .quad   _eita_handler_sstore
    .quad   _eita_handler_jump
    .quad   _eita_handler_jumpi
    .quad   _eita_handler_pc
    .quad   _eita_handler_msize
    .quad   _eita_handler_gas
    .quad   _eita_handler_jumpdest
    .quad   _eita_handler_tload
    .quad   _eita_handler_tstore
    .quad   _eita_handler_mcopy
    .quad   _eita_handler_push0
    .quad   _eita_handler_push1
    .quad   _eita_handler_push2
    .quad   _eita_handler_push3
    .quad   _eita_handler_push4
    .quad   _eita_handler_push5
    .quad   _eita_handler_push6
    .quad   _eita_handler_push7
    .quad   _eita_handler_push8
    .quad   _eita_handler_push9
    .quad   _eita_handler_push10
    .quad   _eita_handler_push11
    .quad   _eita_handler_push12
    .quad   _eita_handler_push13
    .quad   _eita_handler_push14
    .quad   _eita_handler_push15
    .quad   _eita_handler_push16
    .quad   _eita_handler_push17
    .quad   _eita_handler_push18
    .quad   _eita_handler_push19
    .quad   _eita_handler_push20
    .quad   _eita_handler_push21
    .quad   _eita_handler_push22
    .quad   _eita_handler_push23
    .quad   _eita_handler_push24
    .quad   _eita_handler_push25
    .quad   _eita_handler_push26
    .quad   _eita_handler_push27
    .quad   _eita_handler_push28
    .quad   _eita_handler_push29
    .quad   _eita_handler_push30
    .quad   _eita_handler_push31
    .quad   _eita_handler_push32
    .quad   _eita_handler_dup1
    .quad   _eita_handler_dup2
    .quad   _eita_handler_dup3
    .quad   _eita_handler_dup4
    .quad   _eita_handler_dup5
    .quad   _eita_handler_dup6
    .quad   _eita_handler_dup7
    .quad   _eita_handler_dup8
    .quad   _eita_handler_dup9
    .quad   _eita_handler_dup10
    .quad   _eita_handler_dup11
    .quad   _eita_handler_dup12
    .quad   _eita_handler_dup13
    .quad   _eita_handler_dup14
    .quad   _eita_handler_dup15
    .quad   _eita_handler_dup16
    .quad   _eita_handler_swap1
    .quad   _eita_handler_swap2
    .quad   _eita_handler_swap3
    .quad   _eita_handler_swap4
    .quad   _eita_handler_swap5
    .quad   _eita_handler_swap6
    .quad   _eita_handler_swap7
    .quad   _eita_handler_swap8
    .quad   _eita_handler_swap9
    .quad   _eita_handler_swap10
    .quad   _eita_handler_swap11
    .quad   _eita_handler_swap12
    .quad   _eita_handler_swap13
    .quad   _eita_handler_swap14
    .quad   _eita_handler_swap15
    .quad   _eita_handler_swap16
    .quad   _eita_handler_log0
    .quad   _eita_handler_log1
    .quad   _eita_handler_log2
    .quad   _eita_handler_log3
    .quad   _eita_handler_log4
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_create
    .quad   _eita_handler_call
    .quad   _eita_handler_callcode
    .quad   _eita_handler_return
    .quad   _eita_handler_delegatecall
    .quad   _eita_handler_create2
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_staticcall
    .quad   _eita_handler_invalid
    .quad   _eita_handler_invalid
    .quad   _eita_handler_revert
    .quad   _eita_handler_invalid
    .quad   _eita_handler_selfdestruct
.data
.global _eita_fork_tables
.p2align 3
_eita_fork_tables:
    .quad   _eita_dispatch_table_frontier
    .quad   _eita_dispatch_table_homestead
    .quad   _eita_dispatch_table_dao_fork
    .quad   _eita_dispatch_table_tangerine_whistle
    .quad   _eita_dispatch_table_spurious_dragon
    .quad   _eita_dispatch_table_byzantium
    .quad   _eita_dispatch_table_constantinople
    .quad   _eita_dispatch_table_petersburg
    .quad   _eita_dispatch_table_istanbul
    .quad   _eita_dispatch_table_muir_glacier
    .quad   _eita_dispatch_table_berlin
    .quad   _eita_dispatch_table_london
    .quad   _eita_dispatch_table_arrow_glacier
    .quad   _eita_dispatch_table_gray_glacier
    .quad   _eita_dispatch_table_paris
    .quad   _eita_dispatch_table_shanghai
    .quad   _eita_dispatch_table
    .quad   _eita_dispatch_table
    .quad   _eita_dispatch_table_osaka
    .quad   _eita_dispatch_table_osaka
    .quad   _eita_dispatch_table_osaka
    .quad   _eita_dispatch_table_osaka
.section __TEXT,__text,regular,pure_instructions
.global _eita_set_fork
.p2align 2
_eita_set_fork:
    mov   x1, #21
    cmp   x0, x1
    csel  x0, x0, x1, ls
    adrp  x1, _eita_fork_tables@PAGE
    add   x1, x1, _eita_fork_tables@PAGEOFF
    ldr   x1, [x1, x0, lsl #3]
    adrp  x2, _eita_dispatch_ptr@PAGE
    add   x2, x2, _eita_dispatch_ptr@PAGEOFF
    str   x1, [x2]
    ret

.section __TEXT,__text,regular,pure_instructions
.global _eita_call_gas
.p2align 2
_eita_call_gas:
    movz  x9, #100
    movz  x10, #2600
    tst   x1, #1
    csel  x9, x10, x9, ne
    movz  x10, #9000
    tst   x1, #2
    csel  x10, x10, xzr, ne
    add   x9, x9, x10
    movz  x10, #25000
    tst   x1, #4
    csel  x10, x10, xzr, ne
    add   x9, x9, x10
    add   x9, x9, x2
    subs  x11, x4, x9
    csel  x11, xzr, x11, lo
    lsr   x12, x11, #6
    sub   x12, x11, x12
    cmp   x3, x12
    csel  x12, x3, x12, lo
    movz  x13, #2300
    tst   x1, #2
    csel  x13, x13, xzr, ne
    stp   x9, x12, [x0]
    str   x13, [x0, #16]
    ret

.global _eita_call_gas_frontier
.p2align 2
_eita_call_gas_frontier:
    movz  x9, #40
    movz  x10, #9000
    tst   x1, #2
    csel  x10, x10, xzr, ne
    add   x9, x9, x10
    movz  x10, #25000
    tst   x1, #4
    csel  x10, x10, xzr, ne
    add   x9, x9, x10
    mov   x12, x3
    movz  x13, #2300
    tst   x1, #2
    csel  x13, x13, xzr, ne
    stp   x9, x12, [x0]
    str   x13, [x0, #16]
    ret

.global _eita_call_gas_tangerine
.p2align 2
_eita_call_gas_tangerine:
    movz  x9, #700
    movz  x10, #9000
    tst   x1, #2
    csel  x10, x10, xzr, ne
    add   x9, x9, x10
    movz  x10, #25000
    tst   x1, #4
    csel  x10, x10, xzr, ne
    add   x9, x9, x10
    subs  x11, x4, x9
    csel  x11, xzr, x11, lo
    lsr   x12, x11, #6
    sub   x12, x11, x12
    cmp   x3, x12
    csel  x12, x3, x12, lo
    movz  x13, #2300
    tst   x1, #2
    csel  x13, x13, xzr, ne
    stp   x9, x12, [x0]
    str   x13, [x0, #16]
    ret

.section __TEXT,__text,regular,pure_instructions

.global _eita_sstore_gas_legacy
.p2align 2
_eita_sstore_gas_legacy:
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x3, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x11, eq
    ldp   x6, x7, [x4]
    ldp   x8, x9, [x4, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x12, eq
    movz  x16, #5000
    movz  x17, #20000
    eor   x9, x12, #1
    and   x9, x9, x11
    cmp   x9, #0
    csel  x16, x16, x17, eq
    eor   x9, x11, #1
    and   x9, x9, x12
    movz  x8, #15000
    cmp   x9, #0
    csel  x8, xzr, x8, eq
    add   x17, x1, x8
    stp   x16, x17, [x0]
    ret

.global _eita_sstore_gas_eip1283
.p2align 2
_eita_sstore_gas_eip1283:
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x2, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x10, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x3, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x11, eq
    ldp   x6, x7, [x4]
    ldp   x8, x9, [x4, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x12, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x3]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x3, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x13, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x3, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x14, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x15, eq
    cbz   x14, 1f
    movz  x16, #200
    mov   x17, x1
    b     9f
1:
    cbz   x13, 2f
    cbz   x10, 3f
    movz  x16, #20000
    mov   x17, x1
    b     9f
3:
    movz  x16, #5000
    movz  x8, #15000
    cmp   x12, #0
    csel  x8, xzr, x8, eq
    add   x17, x1, x8
    b     9f
2:
    movz  x16, #200
    mov   x9, #0
    cbnz  x10, 4f
    cbz   x11, 5f
    movz  x8, #15000
    sub   x9, x9, x8
5:
    cbz   x12, 4f
    movz  x8, #15000
    add   x9, x9, x8
4:
    cbz   x15, 6f
    movz  x8, #4800
    movz  x7, #19800
    cmp   x10, #0
    csel  x8, x7, x8, ne
    add   x9, x9, x8
6:
    add   x17, x1, x9
    cmp   x17, #0
    csel  x17, xzr, x17, lt
9:
    stp   x16, x17, [x0]
    ret

.global _eita_sstore_gas_eip2200
.p2align 2
_eita_sstore_gas_eip2200:
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x2, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x10, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x3, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x11, eq
    ldp   x6, x7, [x4]
    ldp   x8, x9, [x4, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x12, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x3]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x3, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x13, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x3, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x14, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x15, eq
    movz  x16, #800
    mov   x17, x1
    cbnz  x14, 9f
    cbz   x13, 1f
    movz  x8, #20000
    movz  x9, #5000
    cmp   x10, #0
    csel  x16, x8, x9, ne
1:
    cbnz  x10, 2f
    cbnz  x11, 2f
    cbz   x12, 2f
    movz  x8, #15000
    add   x17, x17, x8
2:
    cbnz  x10, 3f
    cbz   x11, 3f
    movz  x8, #15000
    subs  x9, x17, x8
    csel  x17, xzr, x9, lo
3:
    cbz   x15, 9f
    movz  x8, #19200
    movz  x9, #4200
    cmp   x10, #0
    csel  x8, x8, x9, ne
    add   x17, x17, x8
9:
    stp   x16, x17, [x0]
    ret

.global _eita_sstore_gas_berlin
.p2align 2
_eita_sstore_gas_berlin:
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x2, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x10, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x3, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x11, eq
    ldp   x6, x7, [x4]
    ldp   x8, x9, [x4, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x12, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x3]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x3, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x13, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x3, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x14, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x15, eq
    movz  x16, #100
    mov   x7, #0
    mov   x9, #0
    cbnz  x14, 8f
    cbz   x13, 1f
    movz  x8, #20000
    movz  x6, #2900
    cmp   x10, #0
    csel  x16, x8, x6, ne
    cbnz  x10, 8f
    cbz   x12, 8f
    movz  x7, #15000
    b     8f
1:
    cbnz  x10, 2f
    cbz   x11, 3f
    movz  x9, #15000
    b     2f
3:
    cbz   x12, 2f
    movz  x7, #15000
2:
    cbz   x15, 8f
    movz  x8, #2800
    movz  x6, #19900
    cmp   x10, #0
    csel  x8, x6, x8, ne
    add   x7, x7, x8
8:
    cbz   x5, 4f
    movz  x8, #2100
    add   x16, x16, x8
4:
    add   x17, x1, x7
    subs  x8, x17, x9
    csel  x17, xzr, x8, lo
    stp   x16, x17, [x0]
    ret

.global _eita_sstore_gas_london
.p2align 2
_eita_sstore_gas_london:
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x2, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x10, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x3, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x11, eq
    ldp   x6, x7, [x4]
    ldp   x8, x9, [x4, #16]
    orr   x6, x6, x7
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x12, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x3]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x3, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x13, eq
    ldp   x6, x7, [x3]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x3, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x14, eq
    ldp   x6, x7, [x2]
    ldp   x8, x9, [x4]
    eor   x6, x6, x8
    eor   x7, x7, x9
    orr   x6, x6, x7
    ldp   x8, x9, [x2, #16]
    ldp   x16, x17, [x4, #16]
    eor   x8, x8, x16
    eor   x9, x9, x17
    orr   x8, x8, x9
    orr   x6, x6, x8
    cmp   x6, #0
    cset  x15, eq
    movz  x16, #100
    mov   x7, #0
    mov   x9, #0
    cbnz  x14, 8f
    cbz   x13, 1f
    movz  x8, #20000
    movz  x6, #2900
    cmp   x10, #0
    csel  x16, x8, x6, ne
    cbnz  x10, 8f
    cbz   x12, 8f
    movz  x7, #4800
    b     8f
1:
    cbnz  x10, 2f
    cbz   x11, 3f
    movz  x9, #4800
    b     2f
3:
    cbz   x12, 2f
    movz  x7, #4800
2:
    cbz   x15, 8f
    movz  x8, #2800
    movz  x6, #19900
    cmp   x10, #0
    csel  x8, x6, x8, ne
    add   x7, x7, x8
8:
    cbz   x5, 4f
    movz  x8, #2100
    add   x16, x16, x8
4:
    add   x17, x1, x7
    subs  x8, x17, x9
    csel  x17, xzr, x8, lo
    stp   x16, x17, [x0]
    ret
.data
.global _eita_access_costs
.p2align 3
_eita_access_costs:
    // frontier
    .quad 50, 50    // sload
    .quad 20, 20    // balance
    .quad 20, 20    // extcode
    .quad 0, 0    // extcodehash
    // homestead
    .quad 50, 50    // sload
    .quad 20, 20    // balance
    .quad 20, 20    // extcode
    .quad 0, 0    // extcodehash
    // dao_fork
    .quad 50, 50    // sload
    .quad 20, 20    // balance
    .quad 20, 20    // extcode
    .quad 0, 0    // extcodehash
    // tangerine_whistle
    .quad 200, 200    // sload
    .quad 400, 400    // balance
    .quad 700, 700    // extcode
    .quad 0, 0    // extcodehash
    // spurious_dragon
    .quad 200, 200    // sload
    .quad 400, 400    // balance
    .quad 700, 700    // extcode
    .quad 0, 0    // extcodehash
    // byzantium
    .quad 200, 200    // sload
    .quad 400, 400    // balance
    .quad 700, 700    // extcode
    .quad 0, 0    // extcodehash
    // constantinople
    .quad 200, 200    // sload
    .quad 400, 400    // balance
    .quad 700, 700    // extcode
    .quad 400, 400    // extcodehash
    // petersburg
    .quad 200, 200    // sload
    .quad 400, 400    // balance
    .quad 700, 700    // extcode
    .quad 400, 400    // extcodehash
    // istanbul
    .quad 800, 800    // sload
    .quad 700, 700    // balance
    .quad 700, 700    // extcode
    .quad 700, 700    // extcodehash
    // muir_glacier
    .quad 800, 800    // sload
    .quad 700, 700    // balance
    .quad 700, 700    // extcode
    .quad 700, 700    // extcodehash
    // berlin
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // london
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // arrow_glacier
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // gray_glacier
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // paris
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // shanghai
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // cancun
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // prague
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // osaka
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // bpo1
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // bpo2
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash
    // amsterdam
    .quad 2100, 100    // sload
    .quad 2600, 100    // balance
    .quad 2600, 100    // extcode
    .quad 2600, 100    // extcodehash

.section __TEXT,__text,regular,pure_instructions
.global _eita_execute_program
.p2align 2
_eita_execute_program:
    stp   x29, x30, [sp, #-48]!
    mov   x29, sp
    stp   x19, x20, [sp, #16]
    stp   x21, x22, [sp, #32]
    mov   x19, x0
    mov   x20, x1
    mov   x21, x2
    mov   x22, x3
Lrp_loop:
    ldrb  w9, [x19, #128]
    cbnz  w9, Lrp_halted
    cbz   x22, Lrp_fuel
    sub   x22, x22, #1
    ldr   x9, [x19, #0]
    ldr   x10, [x20]
    cmp   x9, x10
    b.hs  Lrp_miss
    add   x11, x20, #8
    ldr   x1, [x11, x9, lsl #3]
    cbz   x1, Lrp_miss
    mov   x0, x19
    blr   x21
    b     Lrp_loop
Lrp_halted:
    mov   x0, #0
    b     Lrp_ret
Lrp_miss:
    mov   x0, #1
    b     Lrp_ret
Lrp_fuel:
    mov   x0, #2
Lrp_ret:
    ldp   x21, x22, [sp, #32]
    ldp   x19, x20, [sp, #16]
    ldp   x29, x30, [sp], #48
    ret

