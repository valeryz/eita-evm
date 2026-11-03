.text
.intel_syntax noprefix
.globl eita_run_one
.p2align 4
eita_run_one:
    push  rbx
    push  rbp
    push  r12
    push  r13
    push  r14
    push  r15
    mov   rbx, rdi
    mov   rbp, qword ptr [rbx]
    mov   r15, qword ptr [rbx + 8]
    mov   r13, qword ptr [rbx + 16]
    shl   r13, 5
    mov   r12, qword ptr [rbx + 32]
    mov   r14, qword ptr [rbx + 64]
    mov   qword ptr [rbx + 544], rsp
    cmp   r13, 0
    je    Lrc0_1
    mov   r8, qword ptr [r12 + r13 - 32]
    mov   r9, qword ptr [r12 + r13 - 24]
    mov   r10, qword ptr [r12 + r13 - 16]
    mov   r11, qword ptr [r12 + r13 - 8]
Lrc0_1:
    add   rbp, 1
    lea   rax, [rip + eita_dispatch_ptr]
    mov   rax, qword ptr [rax]
    mov   rax, qword ptr [rax + rsi*8]
    call  rax
    jmp   eita_sync_and_ret

.globl eita_run
.p2align 4
eita_run:
    push  rbx
    push  rbp
    push  r12
    push  r13
    push  r14
    push  r15
    mov   rbx, rdi
    mov   rbp, qword ptr [rbx]
    mov   r15, qword ptr [rbx + 8]
    mov   r13, qword ptr [rbx + 16]
    shl   r13, 5
    mov   r12, qword ptr [rbx + 32]
    mov   r14, qword ptr [rbx + 64]
    mov   qword ptr [rbx + 544], rsp
    cmp   r13, 0
    je    Lrc0_r
    mov   r8, qword ptr [r12 + r13 - 32]
    mov   r9, qword ptr [r12 + r13 - 24]
    mov   r10, qword ptr [r12 + r13 - 16]
    mov   r11, qword ptr [r12 + r13 - 8]
Lrc0_r:
Lnext:
    mov   rax, qword ptr [rbx + 496]
    mov   rax, qword ptr [rax + 112]
    cmp   rax, 0
    je    Lfetch
    push  r8
    push  r9
    push  r10
    push  r11
    sub   rsp, 8
    mov   rdi, rbx
    mov   rsi, rbp
    mov   rdx, r15
    mov   rcx, r13
    shr   rcx, 5
    movzx  r8, byte ptr [r14 + rbp]
    call  rax
    add   rsp, 8
    pop   r11
    pop   r10
    pop   r9
    pop   r8
Lfetch:
    movzx  rcx, byte ptr [r14 + rbp]
    add   rbp, 1
    lea   rax, [rip + eita_dispatch_ptr]
    mov   rax, qword ptr [rax]
    mov   rax, qword ptr [rax + rcx*8]
    call  rax
    jmp   Lnext

.globl eita_sync_and_ret
.p2align 4
eita_sync_and_ret:
    mov   rsp, qword ptr [rbx + 544]
    mov   qword ptr [rbx], rbp
    mov   qword ptr [rbx + 8], r15
    mov   rax, r13
    shr   rax, 5
    mov   qword ptr [rbx + 16], rax
    cmp   r13, 0
    je    Lsr0
    mov   qword ptr [r12 + r13 - 32], r8
    mov   qword ptr [r12 + r13 - 24], r9
    mov   qword ptr [r12 + r13 - 16], r10
    mov   qword ptr [r12 + r13 - 8], r11
Lsr0:
    pop   r15
    pop   r14
    pop   r13
    pop   r12
    pop   rbp
    pop   rbx
    ret

.globl eita_oog
.p2align 4
eita_oog:
    mov   rsp, qword ptr [rbx + 544]
    mov   r15, 0
    mov   rax, 1
    mov   byte ptr [rbx + 128], al
    mov   byte ptr [rbx + 129], al
    jmp   eita_sync_and_ret

.globl eita_stack_overflow
.p2align 4
eita_stack_overflow:
    mov   rsp, qword ptr [rbx + 544]
    mov   r15, 0
    mov   rax, 1
    mov   byte ptr [rbx + 128], al
    mov   byte ptr [rbx + 129], al
    jmp   eita_sync_and_ret

.globl eita_stack_underflow
.p2align 4
eita_stack_underflow:
    mov   rsp, qword ptr [rbx + 544]
    mov   r15, 0
    mov   rax, 1
    mov   byte ptr [rbx + 128], al
    mov   byte ptr [rbx + 129], al
    jmp   eita_sync_and_ret

.globl eita_static_violation
.p2align 4
eita_static_violation:
    mov   rsp, qword ptr [rbx + 544]
    mov   r15, 0
    mov   rax, 1
    mov   byte ptr [rbx + 128], al
    mov   byte ptr [rbx + 129], al
    jmp   eita_sync_and_ret

.globl eita_invalid_jump
.p2align 4
eita_invalid_jump:
    jmp   eita_oog

.globl eita_handler_add
.p2align 4
eita_handler_add:
    cmp   r13, 64
    jb    eita_stack_underflow
    add   r8, [r12 + r13 - 64]
    adc   r9, [r12 + r13 - 56]
    adc   r10, [r12 + r13 - 48]
    adc   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_sub
.p2align 4
eita_handler_sub:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   r8, [r12 + r13 - 64]
    sbb   r9, [r12 + r13 - 56]
    sbb   r10, [r12 + r13 - 48]
    sbb   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_and
.p2align 4
eita_handler_and:
    cmp   r13, 64
    jb    eita_stack_underflow
    and   r8, [r12 + r13 - 64]
    and   r9, [r12 + r13 - 56]
    and   r10, [r12 + r13 - 48]
    and   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_or
.p2align 4
eita_handler_or:
    cmp   r13, 64
    jb    eita_stack_underflow
    or    r8, [r12 + r13 - 64]
    or    r9, [r12 + r13 - 56]
    or    r10, [r12 + r13 - 48]
    or    r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_xor
.p2align 4
eita_handler_xor:
    cmp   r13, 64
    jb    eita_stack_underflow
    xor   r8, [r12 + r13 - 64]
    xor   r9, [r12 + r13 - 56]
    xor   r10, [r12 + r13 - 48]
    xor   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_lt
.p2align 4
eita_handler_lt:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   r8, [r12 + r13 - 64]
    mov   rcx, r9
    sbb   rcx, [r12 + r13 - 56]
    mov   rcx, r10
    sbb   rcx, [r12 + r13 - 48]
    mov   rcx, r11
    sbb   rcx, [r12 + r13 - 40]
    setb  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_gt
.p2align 4
eita_handler_gt:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   [r12 + r13 - 64], r8
    mov   rcx, [r12 + r13 - 56]
    sbb   rcx, r9
    mov   rcx, [r12 + r13 - 48]
    sbb   rcx, r10
    mov   rcx, [r12 + r13 - 40]
    sbb   rcx, r11
    setb  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_eq
.p2align 4
eita_handler_eq:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, r8
    xor   rcx, [r12 + r13 - 64]
    mov   rdx, r9
    xor   rdx, [r12 + r13 - 56]
    or    rcx, rdx
    mov   rdx, r10
    xor   rdx, [r12 + r13 - 48]
    or    rcx, rdx
    mov   rdx, r11
    xor   rdx, [r12 + r13 - 40]
    or    rcx, rdx
    cmp   rcx, 0
    sete  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_iszero
.p2align 4
eita_handler_iszero:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r8
    or    rcx, r9
    mov   rdx, r10
    or    rdx, r11
    or    rcx, rdx
    cmp   rcx, 0
    sete  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_clz
.p2align 4
eita_handler_clz:
    cmp   r13, 32
    jb    eita_stack_underflow
    lzcnt rax, r11
    lzcnt rcx, r10
    lzcnt rdx, r9
    lzcnt rsi, r8
    add   rcx, 64
    add   rdx, 128
    add   rsi, 192
    cmp   r9, 0
    cmove rdx, rsi
    cmp   r10, 0
    cmove rcx, rdx
    cmp   r11, 0
    mov   r8, rcx
    cmovne r8, rax
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_not
.p2align 4
eita_handler_not:
    cmp   r13, 32
    jb    eita_stack_underflow
    not   r8
    not   r9
    not   r10
    not   r11
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_pop
.p2align 4
eita_handler_pop:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   r8, [r12 + r13 - 64]
    mov   r9, [r12 + r13 - 56]
    mov   r10, [r12 + r13 - 48]
    mov   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_stop
.p2align 4
eita_handler_stop:
    sub   rbp, 1
    mov   rcx, 1
    mov   byte ptr [rbx + 128], cl
    jmp   eita_sync_and_ret

.globl eita_handler_jumpdest
.p2align 4
eita_handler_jumpdest:
    sub   r15, 1
    jb    eita_oog
    ret

.globl eita_handler_invalid
.p2align 4
eita_handler_invalid:
    jmp   eita_oog

.globl eita_handler_address
.p2align 4
eita_handler_address:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 144]
    mov   r9, [rbx + 152]
    mov   r10, [rbx + 160]
    mov   r11, [rbx + 168]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_origin
.p2align 4
eita_handler_origin:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 176]
    mov   r9, [rbx + 184]
    mov   r10, [rbx + 192]
    mov   r11, [rbx + 200]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_caller
.p2align 4
eita_handler_caller:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 208]
    mov   r9, [rbx + 216]
    mov   r10, [rbx + 224]
    mov   r11, [rbx + 232]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_coinbase
.p2align 4
eita_handler_coinbase:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 336]
    mov   r9, [rbx + 344]
    mov   r10, [rbx + 352]
    mov   r11, [rbx + 360]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_callvalue
.p2align 4
eita_handler_callvalue:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 240]
    mov   r9, [rbx + 248]
    mov   r10, [rbx + 256]
    mov   r11, [rbx + 264]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_gasprice
.p2align 4
eita_handler_gasprice:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 272]
    mov   r9, [rbx + 280]
    mov   r10, [rbx + 288]
    mov   r11, [rbx + 296]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_chainid
.p2align 4
eita_handler_chainid:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 304]
    mov   r9, [rbx + 312]
    mov   r10, [rbx + 320]
    mov   r11, [rbx + 328]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_timestamp
.p2align 4
eita_handler_timestamp:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 368]
    mov   r9, [rbx + 376]
    mov   r10, [rbx + 384]
    mov   r11, [rbx + 392]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_number
.p2align 4
eita_handler_number:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 400]
    mov   r9, [rbx + 408]
    mov   r10, [rbx + 416]
    mov   r11, [rbx + 424]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_gaslimit
.p2align 4
eita_handler_gaslimit:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 432]
    mov   r9, [rbx + 440]
    mov   r10, [rbx + 448]
    mov   r11, [rbx + 456]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_basefee
.p2align 4
eita_handler_basefee:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 464]
    mov   r9, [rbx + 472]
    mov   r10, [rbx + 480]
    mov   r11, [rbx + 488]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_prevrandao
.p2align 4
eita_handler_prevrandao:
    cmp   r13, 32768
    jae   eita_stack_overflow
    lea   rcx, [rbx + 512]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_blobhash
.p2align 4
eita_handler_blobhash:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   .Lbh_zero
    mov   rcx, [rbx + 560]
    cmp   r8, rcx
    jae   .Lbh_zero
    mov   rdx, [rbx + 552]
    mov   rcx, r8
    shl   rcx, 5
    add   rcx, rdx
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    jmp   .Lbh_done
.Lbh_zero:
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
.Lbh_done:
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_blobbasefee
.p2align 4
eita_handler_blobbasefee:
    cmp   r13, 32768
    jae   eita_stack_overflow
    lea   rcx, [rbx + 568]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_pc
.p2align 4
eita_handler_pc:
    cmp   r13, 32768
    jae   eita_stack_overflow
    lea   r8, [rbp - 1]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_msize
.p2align 4
eita_handler_msize:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 48]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_gas
.p2align 4
eita_handler_gas:
    cmp   r13, 32768
    jae   eita_stack_overflow
    sub   r15, 2
    jb    eita_oog
    mov   r8, r15
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    ret

.globl eita_handler_calldatasize
.p2align 4
eita_handler_calldatasize:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 88]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_codesize
.p2align 4
eita_handler_codesize:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 72]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_returndatasize
.p2align 4
eita_handler_returndatasize:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 104]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_sstore
.p2align 4
eita_handler_sstore:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 2300
    cmp   r15, rcx
    jbe   eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rbx + 496]
    mov   rax, [rax + 8]
    call  rax
    sub   r15, rax
    jb    eita_oog
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 16]
    mov   rsi, 104
    mov   rax, rdx
    imul  rax, rsi
    add   rax, rdi
    add   rdx, 1
    mov   [rcx + 0], rdx
    mov   qword ptr [rax + 0], 0
    mov   rdx, [rbx + 144]
    mov   rsi, [rbx + 152]
    mov   [rax + 8], rdx
    mov   [rax + 16], rsi
    mov   rdi, [rbx + 160]
    mov   rsi, [rbx + 168]
    mov   [rax + 24], rdi
    mov   [rax + 32], rsi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    mov   [rax + 40], r8
    mov   [rax + 48], r9
    mov   [rax + 56], r10
    mov   [rax + 64], r11
    mov   rcx, [r12 + r13 - 64]
    mov   [rax + 72], rcx
    mov   rcx, [r12 + r13 - 56]
    mov   [rax + 80], rcx
    mov   rcx, [r12 + r13 - 48]
    mov   [rax + 88], rcx
    mov   rcx, [r12 + r13 - 40]
    mov   [rax + 96], rcx
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_slt
.p2align 4
eita_handler_slt:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   r8, [r12 + r13 - 64]
    mov   rcx, r9
    sbb   rcx, [r12 + r13 - 56]
    mov   rcx, r10
    sbb   rcx, [r12 + r13 - 48]
    mov   rcx, r11
    sbb   rcx, [r12 + r13 - 40]
    setl  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_sgt
.p2align 4
eita_handler_sgt:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   [r12 + r13 - 64], r8
    mov   rcx, [r12 + r13 - 56]
    sbb   rcx, r9
    mov   rcx, [r12 + r13 - 48]
    sbb   rcx, r10
    mov   rcx, [r12 + r13 - 40]
    sbb   rcx, r11
    setl  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_mul
.p2align 4
eita_handler_mul:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_mul]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_div
.p2align 4
eita_handler_div:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_div]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_sdiv
.p2align 4
eita_handler_sdiv:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_sdiv]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_mod
.p2align 4
eita_handler_mod:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_mod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_smod
.p2align 4
eita_handler_smod:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_smod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_exp
.p2align 4
eita_handler_exp:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 0
    cmp   qword ptr [r12 + r13 - 40], 0
    jz    .Lexp_l2
    lzcnt rdx, qword ptr [r12 + r13 - 40]
    mov   rcx, 256
    sub   rcx, rdx
    jmp   .Lexp_charge
.Lexp_l2:
    cmp   qword ptr [r12 + r13 - 48], 0
    jz    .Lexp_l1
    lzcnt rdx, qword ptr [r12 + r13 - 48]
    mov   rcx, 192
    sub   rcx, rdx
    jmp   .Lexp_charge
.Lexp_l1:
    cmp   qword ptr [r12 + r13 - 56], 0
    jz    .Lexp_l0
    lzcnt rdx, qword ptr [r12 + r13 - 56]
    mov   rcx, 128
    sub   rcx, rdx
    jmp   .Lexp_charge
.Lexp_l0:
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    .Lexp_zero_e
    lzcnt rdx, qword ptr [r12 + r13 - 64]
    mov   rcx, 64
    sub   rcx, rdx
.Lexp_charge:
    add   rcx, 7
    shr   rcx, 3
    jmp   .Lexp_do_gas
.Lexp_zero_e:
    mov   rcx, 0
.Lexp_do_gas:
    mov   rdx, 50
    imul  rcx, rdx
    add   rcx, 10
    sub   r15, rcx
    jb    eita_oog
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_exp]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_shl
.p2align 4
eita_handler_shl:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_shl]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_shr
.p2align 4
eita_handler_shr:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_shr]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_sar
.p2align 4
eita_handler_sar:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_sar]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_byte
.p2align 4
eita_handler_byte:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_byte]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_signextend
.p2align 4
eita_handler_signextend:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_signextend]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_addmod
.p2align 4
eita_handler_addmod:
    cmp   r13, 96
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_addmod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 8
    jb    eita_oog
    ret

.globl eita_handler_mulmod
.p2align 4
eita_handler_mulmod:
    cmp   r13, 96
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_mulmod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 8
    jb    eita_oog
    ret

.globl eita_handler_calldataload
.p2align 4
eita_handler_calldataload:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    mov   rsi, rbx
    lea   rdx, [r13 - 32]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_calldataload]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_calldatacopy
.p2align 4
eita_handler_calldatacopy:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rdi, [rdx + 8]
    mov   rax, [rdx + 16]
    or    rdi, rax
    mov   rax, [rdx + 24]
    or    rdi, rax
    cmp   rdi, 0
    jnz   eita_oog
    mov   rsi, 3
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rcx, 0
    jz    6f
    mov   rdi, r9
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, rcx
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_calldatacopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_codecopy
.p2align 4
eita_handler_codecopy:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rdi, [rdx + 8]
    mov   rax, [rdx + 16]
    or    rdi, rax
    mov   rax, [rdx + 24]
    or    rdi, rax
    cmp   rdi, 0
    jnz   eita_oog
    mov   rsi, 3
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rcx, 0
    jz    6f
    mov   rdi, r9
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, rcx
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_codecopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_returndatacopy
.p2align 4
eita_handler_returndatacopy:
    cmp   r13, 96
    jb    eita_stack_underflow
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx + 8]
    mov   rdi, [rcx + 16]
    or    rdx, rdi
    mov   rdi, [rcx + 24]
    or    rdx, rdi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rdx, [rcx + 0]
    add   rdx, [r12 + r13 - 64]
    jc    eita_oog
    mov   rdi, [rbx + 104]
    cmp   rdx, rdi
    ja    eita_oog
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rdi, [rdx + 8]
    mov   rax, [rdx + 16]
    or    rdi, rax
    mov   rax, [rdx + 24]
    or    rdi, rax
    cmp   rdi, 0
    jnz   eita_oog
    mov   rsi, 3
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rcx, 0
    jz    6f
    mov   rdi, r9
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, rcx
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_returndatacopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_mcopy
.p2align 4
eita_handler_mcopy:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lmcd0
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lmcd1
.Lmcd0:
    mov   rax, 0
.Lmcd1:
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 64]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lmcs0
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rcx, rsi
    add   rcx, rdi
    jc    eita_oog
    jmp   .Lmcs1
.Lmcs0:
    mov   rcx, 0
.Lmcs1:
    cmp   rax, rcx
    cmovbe rax, rcx
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rsi, 3
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rax, 0
    jz    6f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_mcopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_keccak256
.p2align 4
eita_handler_keccak256:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, [r12 + r13 - 64]
    add   rsi, 31
    cmp   rsi, [r12 + r13 - 64]
    jb    eita_oog
    shr   rsi, 5
    lea   rsi, [rsi + rsi*2]
    add   rsi, rsi
    add   rsi, 30
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    sub   r15, rsi
    jb    eita_oog
    sub   rsp, 32
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [rsp + 0]
    call  qword ptr [rip + Lsym_eita_helper_keccak256]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_sload
.p2align 4
eita_handler_sload:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 0]
    call  rax
    sub   r15, rax
    jb    eita_oog
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_tload
.p2align 4
eita_handler_tload:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, 100
    sub   r15, rcx
    jb    eita_oog
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    mov   rdi, [rdi + 64]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [rsp + 0]
    call  qword ptr [rip + Lsym_eita_ts_tload]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_balance
.p2align 4
eita_handler_balance:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 32]
    call  rax
    sub   r15, rax
    jb    eita_oog
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_selfbalance
.p2align 4
eita_handler_selfbalance:
    cmp   r13, 32768
    jae   eita_stack_overflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 32]
    call  rax
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 5
    jb    eita_oog
    ret

.globl eita_handler_extcodesize
.p2align 4
eita_handler_extcodesize:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 16
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 40]
    call  rax
    mov   rcx, rax
    sub   r15, rcx
    jb    eita_oog
    mov   r8, [rsp + 0]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   rsp, 16
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_extcodehash
.p2align 4
eita_handler_extcodehash:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 48]
    call  rax
    sub   r15, rax
    jb    eita_oog
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_blockhash
.p2align 4
eita_handler_blockhash:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 64]
    call  rax
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 20
    jb    eita_oog
    ret

.globl eita_handler_extcodecopy
.p2align 4
eita_handler_extcodecopy:
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 64]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lxcd0
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lxcd1
.Lxcd0:
    mov   rax, 0
.Lxcd1:
    mov   rsi, 0
    cmp   rax, 0
    jz    90f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
90:
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   r11, [rcx]
    mov   r10, [rbx + 40]
    mov   rdx, r10
    add   rdx, r11
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   r11, [rcx + 8]
    mov   r10, [rcx + 16]
    or    r11, r10
    mov   r10, [rcx + 24]
    or    r11, r10
    mov   rcx, [rcx]
    cmp   r11, 0
    jz    94f
    mov   rcx, 0
    sub   rcx, 1
94:
    lea   r8, [r13 - 128]
    add   r8, r12
    mov   r8, [r8]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 56]
    call  rax
    sub   r15, rax
    jb    eita_oog
    sub   r13, 128
    cmp   r13, 32
    jl    91f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
91:
    ret

.globl eita_handler_staticcall
.p2align 4
eita_handler_staticcall:
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 96]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfin0_staticcall
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lcfin1_staticcall
.Lcfin0_staticcall:
    mov   rax, 0
.Lcfin1_staticcall:
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 160]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfout0_staticcall
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rcx, rsi
    add   rcx, rdi
    jc    eita_oog
    jmp   .Lcfout1_staticcall
.Lcfout0_staticcall:
    mov   rcx, 0
.Lcfout1_staticcall:
    cmp   rax, rcx
    cmovbe rax, rcx
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    sub   rsp, 192
    mov   [rbx + 0], rbp
    mov   [rbx + 8], r15
    mov   rcx, r13
    shr   rcx, 5
    mov   [rbx + 16], rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rax, 3
    mov   dword ptr [rsp + 0], eax
    mov   rax, 1
    mov   dword ptr [rsp + 4], eax
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 8], rax
    mov   [rsp + 16], rdx
    mov   [rsp + 24], rsi
    mov   [rsp + 32], rdi
    mov   qword ptr [rsp + 40], 0
    mov   qword ptr [rsp + 48], 0
    mov   qword ptr [rsp + 56], 0
    mov   qword ptr [rsp + 64], 0
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, [rbx + 40]
    add   rdx, rdi
    mov   [rsp + 72], rdx
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   [rsp + 80], rdx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    mov   rax, -1
    cmovne rdx, rax
    mov   [rsp + 88], rdx
    mov   qword ptr [rsp + 96], 0
    mov   qword ptr [rsp + 104], 0
    mov   qword ptr [rsp + 112], 0
    mov   qword ptr [rsp + 120], 0
    mov   rdi, [rbx + 504]
    lea   rsi, [rsp + 0]
    lea   rdx, [rsp + 128]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 88]
    call  rax
    mov   rax, [rsp + 136]
    mov   [rbx + 96], rax
    mov   rax, [rsp + 144]
    mov   [rbx + 104], rax
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rsi, [rcx]
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, rbx
    call  qword ptr [rip + Lsym_eita_helper_returndata_to_mem]
    mov   edx, dword ptr [rsp + 128]
    mov   rax, [rsp + 152]
    sub   r13, 160
    mov   r8, rdx
    and   r8, 255
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r15, [rbx + 8]
    sub   r15, rax
    jb    eita_oog
    add   rsp, 192
    ret

.globl eita_handler_call
.p2align 4
eita_handler_call:
    cmp   r13, 224
    jb    eita_stack_underflow
    movzx rcx, byte ptr [rbx + 130]
    cmp   ecx, 0
    jz    93f
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 8]
    or    rdx, rdi
    mov   rdi, [rcx + 16]
    or    rdx, rdi
    mov   rdi, [rcx + 24]
    or    rdx, rdi
    cmp   rdx, 0
    jnz   eita_static_violation
93:
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 128]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfin0_call
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lcfin1_call
.Lcfin0_call:
    mov   rax, 0
.Lcfin1_call:
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 192]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfout0_call
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rcx, rsi
    add   rcx, rdi
    jc    eita_oog
    jmp   .Lcfout1_call
.Lcfout0_call:
    mov   rcx, 0
.Lcfout1_call:
    cmp   rax, rcx
    cmovbe rax, rcx
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    sub   rsp, 192
    mov   [rbx + 0], rbp
    mov   [rbx + 8], r15
    mov   rcx, r13
    shr   rcx, 5
    mov   [rbx + 16], rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rax, 0
    mov   dword ptr [rsp + 0], eax
    mov   rax, 0
    mov   dword ptr [rsp + 4], eax
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 8], rax
    mov   [rsp + 16], rdx
    mov   [rsp + 24], rsi
    mov   [rsp + 32], rdi
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 40], rax
    mov   [rsp + 48], rdx
    mov   [rsp + 56], rsi
    mov   [rsp + 64], rdi
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, [rbx + 40]
    add   rdx, rdi
    mov   [rsp + 72], rdx
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   [rsp + 80], rdx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    mov   rax, -1
    cmovne rdx, rax
    mov   [rsp + 88], rdx
    mov   qword ptr [rsp + 96], 0
    mov   qword ptr [rsp + 104], 0
    mov   qword ptr [rsp + 112], 0
    mov   qword ptr [rsp + 120], 0
    mov   rdi, [rbx + 504]
    lea   rsi, [rsp + 0]
    lea   rdx, [rsp + 128]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 88]
    call  rax
    mov   rax, [rsp + 136]
    mov   [rbx + 96], rax
    mov   rax, [rsp + 144]
    mov   [rbx + 104], rax
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rsi, [rcx]
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, rbx
    call  qword ptr [rip + Lsym_eita_helper_returndata_to_mem]
    mov   edx, dword ptr [rsp + 128]
    mov   rax, [rsp + 152]
    sub   r13, 192
    mov   r8, rdx
    and   r8, 255
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r15, [rbx + 8]
    sub   r15, rax
    jb    eita_oog
    add   rsp, 192
    ret

.globl eita_handler_callcode
.p2align 4
eita_handler_callcode:
    cmp   r13, 224
    jb    eita_stack_underflow
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 128]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfin0_callcode
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lcfin1_callcode
.Lcfin0_callcode:
    mov   rax, 0
.Lcfin1_callcode:
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 192]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfout0_callcode
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rcx, rsi
    add   rcx, rdi
    jc    eita_oog
    jmp   .Lcfout1_callcode
.Lcfout0_callcode:
    mov   rcx, 0
.Lcfout1_callcode:
    cmp   rax, rcx
    cmovbe rax, rcx
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    sub   rsp, 192
    mov   [rbx + 0], rbp
    mov   [rbx + 8], r15
    mov   rcx, r13
    shr   rcx, 5
    mov   [rbx + 16], rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rax, 1
    mov   dword ptr [rsp + 0], eax
    mov   rax, 0
    mov   dword ptr [rsp + 4], eax
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 8], rax
    mov   [rsp + 16], rdx
    mov   [rsp + 24], rsi
    mov   [rsp + 32], rdi
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 40], rax
    mov   [rsp + 48], rdx
    mov   [rsp + 56], rsi
    mov   [rsp + 64], rdi
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, [rbx + 40]
    add   rdx, rdi
    mov   [rsp + 72], rdx
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   [rsp + 80], rdx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    mov   rax, -1
    cmovne rdx, rax
    mov   [rsp + 88], rdx
    mov   qword ptr [rsp + 96], 0
    mov   qword ptr [rsp + 104], 0
    mov   qword ptr [rsp + 112], 0
    mov   qword ptr [rsp + 120], 0
    mov   rdi, [rbx + 504]
    lea   rsi, [rsp + 0]
    lea   rdx, [rsp + 128]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 88]
    call  rax
    mov   rax, [rsp + 136]
    mov   [rbx + 96], rax
    mov   rax, [rsp + 144]
    mov   [rbx + 104], rax
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rsi, [rcx]
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, rbx
    call  qword ptr [rip + Lsym_eita_helper_returndata_to_mem]
    mov   edx, dword ptr [rsp + 128]
    mov   rax, [rsp + 152]
    sub   r13, 192
    mov   r8, rdx
    and   r8, 255
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r15, [rbx + 8]
    sub   r15, rax
    jb    eita_oog
    add   rsp, 192
    ret

.globl eita_handler_delegatecall
.p2align 4
eita_handler_delegatecall:
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 96]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfin0_delegatecall
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lcfin1_delegatecall
.Lcfin0_delegatecall:
    mov   rax, 0
.Lcfin1_delegatecall:
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 160]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcfout0_delegatecall
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rcx, rsi
    add   rcx, rdi
    jc    eita_oog
    jmp   .Lcfout1_delegatecall
.Lcfout0_delegatecall:
    mov   rcx, 0
.Lcfout1_delegatecall:
    cmp   rax, rcx
    cmovbe rax, rcx
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    sub   rsp, 192
    mov   [rbx + 0], rbp
    mov   [rbx + 8], r15
    mov   rcx, r13
    shr   rcx, 5
    mov   [rbx + 16], rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rax, 2
    mov   dword ptr [rsp + 0], eax
    mov   rax, 0
    mov   dword ptr [rsp + 4], eax
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 8], rax
    mov   [rsp + 16], rdx
    mov   [rsp + 24], rsi
    mov   [rsp + 32], rdi
    mov   qword ptr [rsp + 40], 0
    mov   qword ptr [rsp + 48], 0
    mov   qword ptr [rsp + 56], 0
    mov   qword ptr [rsp + 64], 0
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, [rbx + 40]
    add   rdx, rdi
    mov   [rsp + 72], rdx
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   [rsp + 80], rdx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    mov   rax, -1
    cmovne rdx, rax
    mov   [rsp + 88], rdx
    mov   qword ptr [rsp + 96], 0
    mov   qword ptr [rsp + 104], 0
    mov   qword ptr [rsp + 112], 0
    mov   qword ptr [rsp + 120], 0
    mov   rdi, [rbx + 504]
    lea   rsi, [rsp + 0]
    lea   rdx, [rsp + 128]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 88]
    call  rax
    mov   rax, [rsp + 136]
    mov   [rbx + 96], rax
    mov   rax, [rsp + 144]
    mov   [rbx + 104], rax
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rsi, [rcx]
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, rbx
    call  qword ptr [rip + Lsym_eita_helper_returndata_to_mem]
    mov   edx, dword ptr [rsp + 128]
    mov   rax, [rsp + 152]
    sub   r13, 160
    mov   r8, rdx
    and   r8, 255
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r15, [rbx + 8]
    sub   r15, rax
    jb    eita_oog
    add   rsp, 192
    ret

.globl eita_handler_create
.p2align 4
eita_handler_create:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 96
    jb    eita_stack_underflow
    sub   rsp, 192
    mov   [rbx + 0], rbp
    mov   [rbx + 8], r15
    mov   rcx, r13
    shr   rcx, 5
    mov   [rbx + 16], rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 64]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcrin0_create
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lcrin1_create
.Lcrin0_create:
    mov   rax, 0
.Lcrin1_create:
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    mov   [rbx + 8], r15
    mov   rax, 4
    mov   dword ptr [rsp + 0], eax
    mov   dword ptr [rsp + 4], 0
    mov   qword ptr [rsp + 8], 0
    mov   qword ptr [rsp + 16], 0
    mov   qword ptr [rsp + 24], 0
    mov   qword ptr [rsp + 32], 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 40], rax
    mov   [rsp + 48], rdx
    mov   [rsp + 56], rsi
    mov   [rsp + 64], rdi
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, [rbx + 40]
    add   rdx, rdi
    mov   [rsp + 72], rdx
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   [rsp + 80], rdx
    mov   [rsp + 88], r15
    mov   qword ptr [rsp + 96], 0
    mov   qword ptr [rsp + 104], 0
    mov   qword ptr [rsp + 112], 0
    mov   qword ptr [rsp + 120], 0
    mov   rdi, [rbx + 504]
    lea   rsi, [rsp + 0]
    lea   rdx, [rsp + 128]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 96]
    call  rax
    mov   rcx, [rsp + 136]
    mov   [rbx + 96], rcx
    mov   rcx, [rsp + 144]
    mov   [rbx + 104], rcx
    mov   edx, dword ptr [rsp + 128]
    cmp   edx, 0
    jz    L_create_fail
    lea   rcx, [rsp + 160]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    jmp   L_create_done
L_create_fail:
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
L_create_done:
    mov   rax, [rsp + 152]
    mov   r15, [rbx + 8]
    sub   r15, rax
    jb    eita_oog
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    add   rsp, 192
    ret

.globl eita_handler_create2
.p2align 4
eita_handler_create2:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 128
    jb    eita_stack_underflow
    sub   rsp, 192
    mov   [rbx + 0], rbp
    mov   [rbx + 8], r15
    mov   rcx, r13
    shr   rcx, 5
    mov   [rbx + 16], rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 64]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lcrin0_create2
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lcrin1_create2
.Lcrin0_create2:
    mov   rax, 0
.Lcrin1_create2:
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    mov   [rbx + 8], r15
    mov   rax, 5
    mov   dword ptr [rsp + 0], eax
    mov   dword ptr [rsp + 4], 0
    mov   qword ptr [rsp + 8], 0
    mov   qword ptr [rsp + 16], 0
    mov   qword ptr [rsp + 24], 0
    mov   qword ptr [rsp + 32], 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 40], rax
    mov   [rsp + 48], rdx
    mov   [rsp + 56], rsi
    mov   [rsp + 64], rdi
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   rdi, [rbx + 40]
    add   rdx, rdi
    mov   [rsp + 72], rdx
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx]
    mov   [rsp + 80], rdx
    mov   [rsp + 88], r15
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rsp + 96], rax
    mov   [rsp + 104], rdx
    mov   [rsp + 112], rsi
    mov   [rsp + 120], rdi
    mov   rdi, [rbx + 504]
    lea   rsi, [rsp + 0]
    lea   rdx, [rsp + 128]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 96]
    call  rax
    mov   rcx, [rsp + 136]
    mov   [rbx + 96], rcx
    mov   rcx, [rsp + 144]
    mov   [rbx + 104], rcx
    mov   edx, dword ptr [rsp + 128]
    cmp   edx, 0
    jz    L_create2_fail
    lea   rcx, [rsp + 160]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    jmp   L_create2_done
L_create2_fail:
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
L_create2_done:
    mov   rax, [rsp + 152]
    mov   r15, [rbx + 8]
    sub   r15, rax
    jb    eita_oog
    sub   r13, 96
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    add   rsp, 192
    ret

.globl eita_handler_selfdestruct
.p2align 4
eita_handler_selfdestruct:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rbp, 1
    mov   rcx, 5000
    sub   r15, rcx
    jb    eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rdx, rcx
    mov   rax, [rbx + 496]
    mov   rax, [rax + 104]
    call  rax
    sub   r15, rax
    jb    eita_oog
    mov   rcx, 1
    mov   byte ptr [rbx + 128], cl
    sub   r13, 32
    jmp   eita_sync_and_ret

.globl eita_handler_mload
.p2align 4
eita_handler_mload:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, 32
    jc    eita_oog
    mov   rsi, 3
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
    mov   rcx, [rbx + 40]
    lea   rdx, [r8 + 32]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    add   rcx, r8
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    bswap r8
    bswap r9
    bswap r10
    bswap r11
    mov   rcx, r8
    mov   r8, r11
    mov   r11, rcx
    mov   rcx, r9
    mov   r9, r10
    mov   r10, rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    ret

.globl eita_handler_mstore
.p2align 4
eita_handler_mstore:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, 32
    jc    eita_oog
    mov   rsi, 3
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
    lea   rdx, [r8 + 32]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    mov   rcx, [rbx + 40]
    add   rcx, r8
    mov   rax, [r12 + r13 - 40]
    bswap rax
    mov   rdx, [r12 + r13 - 48]
    bswap rdx
    mov   rsi, [r12 + r13 - 56]
    bswap rsi
    mov   rdi, [r12 + r13 - 64]
    bswap rdi
    mov   [rcx + 0], rax
    mov   [rcx + 8], rdx
    mov   [rcx + 16], rsi
    mov   [rcx + 24], rdi
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_mstore8
.p2align 4
eita_handler_mstore8:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, 1
    jc    eita_oog
    mov   rsi, 3
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
    mov   rcx, [rbx + 40]
    lea   rdx, [r8 + 1]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    mov   rax, [r12 + r13 - 64]
    mov   byte ptr [rcx + r8], al
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_return
.p2align 4
eita_handler_return:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rbp, 1
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lror0
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lror1
.Lror0:
    mov   rax, 0
.Lror1:
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    mov   rax, [r12 + r13 - 64]
    mov   [rbx + 120], rax
    mov   rcx, [rbx + 40]
    add   rcx, r8
    mov   [rbx + 112], rcx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    mov   rcx, 1
    mov   byte ptr [rbx + 128], cl
    sub   r13, 64
    jmp   eita_sync_and_ret

.globl eita_handler_revert
.p2align 4
eita_handler_revert:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rbp, 1
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lrov0
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lrov1
.Lrov0:
    mov   rax, 0
.Lrov1:
    mov   rsi, 0
    cmp   rax, 0
    jz    4f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
4:
    mov   rax, [r12 + r13 - 64]
    mov   [rbx + 120], rax
    mov   rcx, [rbx + 40]
    add   rcx, r8
    mov   [rbx + 112], rcx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    mov   rcx, 1
    mov   byte ptr [rbx + 128], cl
    mov   byte ptr [rbx + 129], cl
    sub   r13, 64
    jmp   eita_sync_and_ret

.globl eita_handler_jump
.p2align 4
eita_handler_jump:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_invalid_jump
    mov   rcx, [rbx + 72]
    cmp   r8, rcx
    jae   eita_invalid_jump
    mov   rcx, [rbx + 136]
    movzx rcx, byte ptr [rcx + r8]
    cmp   rcx, 1
    jne   eita_invalid_jump
    mov   rbp, r8
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 8
    jb    eita_oog
    ret

.globl eita_handler_jumpi
.p2align 4
eita_handler_jumpi:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, [r12 + r13 - 64]
    or    rcx, [r12 + r13 - 56]
    mov   rdx, [r12 + r13 - 48]
    or    rdx, [r12 + r13 - 40]
    or    rcx, rdx
    cmp   rcx, 0
    jz    eita_jumpi_fallthrough
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_invalid_jump
    mov   rcx, [rbx + 72]
    cmp   r8, rcx
    jae   eita_invalid_jump
    mov   rcx, [rbx + 136]
    movzx rcx, byte ptr [rcx + r8]
    cmp   rcx, 1
    jne   eita_invalid_jump
    mov   rbp, r8
eita_jumpi_pop:
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 10
    jb    eita_oog
    ret
eita_jumpi_fallthrough:
    jmp   eita_jumpi_pop

.globl eita_handler_tstore
.p2align 4
eita_handler_tstore:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 100
    sub   r15, rcx
    jb    eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rsi, [rbx + 504]
    mov   rdi, [rsi + 64]
    lea   rdx, [rbx + 144]
    lea   rcx, [r13 - 32]
    add   rcx, r12
    lea   r8, [r13 - 64]
    add   r8, r12
    call  qword ptr [rip + Lsym_eita_ts_tstore]
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    ret

.globl eita_handler_push0
.p2align 4
eita_handler_push0:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 2
    jb    eita_oog
    ret

.globl eita_handler_push1
.p2align 4
eita_handler_push1:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 56
    add   rbp, 1
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push2
.p2align 4
eita_handler_push2:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 48
    add   rbp, 2
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push3
.p2align 4
eita_handler_push3:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 40
    add   rbp, 3
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push4
.p2align 4
eita_handler_push4:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 32
    add   rbp, 4
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push5
.p2align 4
eita_handler_push5:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 24
    add   rbp, 5
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push6
.p2align 4
eita_handler_push6:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 16
    add   rbp, 6
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push7
.p2align 4
eita_handler_push7:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 8
    add   rbp, 7
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push8
.p2align 4
eita_handler_push8:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 8
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push9
.p2align 4
eita_handler_push9:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 56
    add   rdx, 1
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 9
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push10
.p2align 4
eita_handler_push10:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 48
    add   rdx, 2
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 10
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push11
.p2align 4
eita_handler_push11:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 40
    add   rdx, 3
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 11
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push12
.p2align 4
eita_handler_push12:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 32
    add   rdx, 4
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 12
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push13
.p2align 4
eita_handler_push13:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 24
    add   rdx, 5
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 13
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push14
.p2align 4
eita_handler_push14:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 16
    add   rdx, 6
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 14
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push15
.p2align 4
eita_handler_push15:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 8
    add   rdx, 7
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 15
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push16
.p2align 4
eita_handler_push16:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 16
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push17
.p2align 4
eita_handler_push17:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 56
    add   rdx, 1
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 17
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push18
.p2align 4
eita_handler_push18:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 48
    add   rdx, 2
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 18
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push19
.p2align 4
eita_handler_push19:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 40
    add   rdx, 3
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 19
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push20
.p2align 4
eita_handler_push20:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 32
    add   rdx, 4
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 20
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push21
.p2align 4
eita_handler_push21:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 24
    add   rdx, 5
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 21
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push22
.p2align 4
eita_handler_push22:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 16
    add   rdx, 6
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 22
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push23
.p2align 4
eita_handler_push23:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 8
    add   rdx, 7
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 23
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push24
.p2align 4
eita_handler_push24:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 24
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push25
.p2align 4
eita_handler_push25:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 56
    add   rdx, 1
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 25
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push26
.p2align 4
eita_handler_push26:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 48
    add   rdx, 2
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 26
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push27
.p2align 4
eita_handler_push27:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 40
    add   rdx, 3
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 27
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push28
.p2align 4
eita_handler_push28:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 32
    add   rdx, 4
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 28
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push29
.p2align 4
eita_handler_push29:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 24
    add   rdx, 5
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 29
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push30
.p2align 4
eita_handler_push30:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 16
    add   rdx, 6
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 30
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push31
.p2align 4
eita_handler_push31:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 8
    add   rdx, 7
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 31
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_push32
.p2align 4
eita_handler_push32:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx + 0]
    bswap r11
    mov   r10, [rdx + 8]
    bswap r10
    mov   r9, [rdx + 16]
    bswap r9
    mov   r8, [rdx + 24]
    bswap r8
    add   rbp, 32
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_log0
.p2align 4
eita_handler_log0:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 375
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 64
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 32]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 0]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 0
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log1
.p2align 4
eita_handler_log1:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 750
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 96
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 64]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 32]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 1
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log2
.p2align 4
eita_handler_log2:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 1125
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 128
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 96]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 64]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 2
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log3
.p2align 4
eita_handler_log3:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 160
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 1500
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 160
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 128]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 96]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 3
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log4
.p2align 4
eita_handler_log4:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 1875
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 192
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 160]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 128]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 4
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_dup1
.p2align 4
eita_handler_dup1:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 32
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup2
.p2align 4
eita_handler_dup2:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup3
.p2align 4
eita_handler_dup3:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup4
.p2align 4
eita_handler_dup4:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup5
.p2align 4
eita_handler_dup5:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 160
    jb    eita_stack_underflow
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup6
.p2align 4
eita_handler_dup6:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup7
.p2align 4
eita_handler_dup7:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 224
    jb    eita_stack_underflow
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup8
.p2align 4
eita_handler_dup8:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 256
    jb    eita_stack_underflow
    lea   rcx, [r13 - 256]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup9
.p2align 4
eita_handler_dup9:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 288
    jb    eita_stack_underflow
    lea   rcx, [r13 - 288]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup10
.p2align 4
eita_handler_dup10:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 320
    jb    eita_stack_underflow
    lea   rcx, [r13 - 320]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup11
.p2align 4
eita_handler_dup11:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 352
    jb    eita_stack_underflow
    lea   rcx, [r13 - 352]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup12
.p2align 4
eita_handler_dup12:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 384
    jb    eita_stack_underflow
    lea   rcx, [r13 - 384]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup13
.p2align 4
eita_handler_dup13:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 416
    jb    eita_stack_underflow
    lea   rcx, [r13 - 416]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup14
.p2align 4
eita_handler_dup14:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 448
    jb    eita_stack_underflow
    lea   rcx, [r13 - 448]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup15
.p2align 4
eita_handler_dup15:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 480
    jb    eita_stack_underflow
    lea   rcx, [r13 - 480]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_dup16
.p2align 4
eita_handler_dup16:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 512
    jb    eita_stack_underflow
    lea   rcx, [r13 - 512]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap1
.p2align 4
eita_handler_swap1:
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap2
.p2align 4
eita_handler_swap2:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap3
.p2align 4
eita_handler_swap3:
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap4
.p2align 4
eita_handler_swap4:
    cmp   r13, 160
    jb    eita_stack_underflow
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap5
.p2align 4
eita_handler_swap5:
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap6
.p2align 4
eita_handler_swap6:
    cmp   r13, 224
    jb    eita_stack_underflow
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap7
.p2align 4
eita_handler_swap7:
    cmp   r13, 256
    jb    eita_stack_underflow
    lea   rcx, [r13 - 256]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap8
.p2align 4
eita_handler_swap8:
    cmp   r13, 288
    jb    eita_stack_underflow
    lea   rcx, [r13 - 288]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap9
.p2align 4
eita_handler_swap9:
    cmp   r13, 320
    jb    eita_stack_underflow
    lea   rcx, [r13 - 320]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap10
.p2align 4
eita_handler_swap10:
    cmp   r13, 352
    jb    eita_stack_underflow
    lea   rcx, [r13 - 352]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap11
.p2align 4
eita_handler_swap11:
    cmp   r13, 384
    jb    eita_stack_underflow
    lea   rcx, [r13 - 384]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap12
.p2align 4
eita_handler_swap12:
    cmp   r13, 416
    jb    eita_stack_underflow
    lea   rcx, [r13 - 416]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap13
.p2align 4
eita_handler_swap13:
    cmp   r13, 448
    jb    eita_stack_underflow
    lea   rcx, [r13 - 448]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap14
.p2align 4
eita_handler_swap14:
    cmp   r13, 480
    jb    eita_stack_underflow
    lea   rcx, [r13 - 480]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap15
.p2align 4
eita_handler_swap15:
    cmp   r13, 512
    jb    eita_stack_underflow
    lea   rcx, [r13 - 512]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_swap16
.p2align 4
eita_handler_swap16:
    cmp   r13, 544
    jb    eita_stack_underflow
    lea   rcx, [r13 - 544]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 3
    jb    eita_oog
    ret

.globl eita_handler_add_f
.p2align 4
eita_handler_add_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    add   r8, [r12 + r13 - 64]
    adc   r9, [r12 + r13 - 56]
    adc   r10, [r12 + r13 - 48]
    adc   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_sub_f
.p2align 4
eita_handler_sub_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   r8, [r12 + r13 - 64]
    sbb   r9, [r12 + r13 - 56]
    sbb   r10, [r12 + r13 - 48]
    sbb   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_and_f
.p2align 4
eita_handler_and_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    and   r8, [r12 + r13 - 64]
    and   r9, [r12 + r13 - 56]
    and   r10, [r12 + r13 - 48]
    and   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_or_f
.p2align 4
eita_handler_or_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    or    r8, [r12 + r13 - 64]
    or    r9, [r12 + r13 - 56]
    or    r10, [r12 + r13 - 48]
    or    r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_xor_f
.p2align 4
eita_handler_xor_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    xor   r8, [r12 + r13 - 64]
    xor   r9, [r12 + r13 - 56]
    xor   r10, [r12 + r13 - 48]
    xor   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_lt_f
.p2align 4
eita_handler_lt_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   r8, [r12 + r13 - 64]
    mov   rcx, r9
    sbb   rcx, [r12 + r13 - 56]
    mov   rcx, r10
    sbb   rcx, [r12 + r13 - 48]
    mov   rcx, r11
    sbb   rcx, [r12 + r13 - 40]
    setb  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_gt_f
.p2align 4
eita_handler_gt_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   [r12 + r13 - 64], r8
    mov   rcx, [r12 + r13 - 56]
    sbb   rcx, r9
    mov   rcx, [r12 + r13 - 48]
    sbb   rcx, r10
    mov   rcx, [r12 + r13 - 40]
    sbb   rcx, r11
    setb  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_eq_f
.p2align 4
eita_handler_eq_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, r8
    xor   rcx, [r12 + r13 - 64]
    mov   rdx, r9
    xor   rdx, [r12 + r13 - 56]
    or    rcx, rdx
    mov   rdx, r10
    xor   rdx, [r12 + r13 - 48]
    or    rcx, rdx
    mov   rdx, r11
    xor   rdx, [r12 + r13 - 40]
    or    rcx, rdx
    cmp   rcx, 0
    sete  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_iszero_f
.p2align 4
eita_handler_iszero_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r8
    or    rcx, r9
    mov   rdx, r10
    or    rdx, r11
    or    rcx, rdx
    cmp   rcx, 0
    sete  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_clz_f
.p2align 4
eita_handler_clz_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    lzcnt rax, r11
    lzcnt rcx, r10
    lzcnt rdx, r9
    lzcnt rsi, r8
    add   rcx, 64
    add   rdx, 128
    add   rsi, 192
    cmp   r9, 0
    cmove rdx, rsi
    cmp   r10, 0
    cmove rcx, rdx
    cmp   r11, 0
    mov   r8, rcx
    cmovne r8, rax
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_not_f
.p2align 4
eita_handler_not_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    not   r8
    not   r9
    not   r10
    not   r11
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_pop_f
.p2align 4
eita_handler_pop_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   r8, [r12 + r13 - 64]
    mov   r9, [r12 + r13 - 56]
    mov   r10, [r12 + r13 - 48]
    mov   r11, [r12 + r13 - 40]
    sub   r13, 32
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_jumpdest_f
.p2align 4
eita_handler_jumpdest_f:
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_address_f
.p2align 4
eita_handler_address_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 144]
    mov   r9, [rbx + 152]
    mov   r10, [rbx + 160]
    mov   r11, [rbx + 168]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_origin_f
.p2align 4
eita_handler_origin_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 176]
    mov   r9, [rbx + 184]
    mov   r10, [rbx + 192]
    mov   r11, [rbx + 200]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_caller_f
.p2align 4
eita_handler_caller_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 208]
    mov   r9, [rbx + 216]
    mov   r10, [rbx + 224]
    mov   r11, [rbx + 232]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_coinbase_f
.p2align 4
eita_handler_coinbase_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 336]
    mov   r9, [rbx + 344]
    mov   r10, [rbx + 352]
    mov   r11, [rbx + 360]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_callvalue_f
.p2align 4
eita_handler_callvalue_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 240]
    mov   r9, [rbx + 248]
    mov   r10, [rbx + 256]
    mov   r11, [rbx + 264]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_gasprice_f
.p2align 4
eita_handler_gasprice_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 272]
    mov   r9, [rbx + 280]
    mov   r10, [rbx + 288]
    mov   r11, [rbx + 296]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_chainid_f
.p2align 4
eita_handler_chainid_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 304]
    mov   r9, [rbx + 312]
    mov   r10, [rbx + 320]
    mov   r11, [rbx + 328]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_timestamp_f
.p2align 4
eita_handler_timestamp_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 368]
    mov   r9, [rbx + 376]
    mov   r10, [rbx + 384]
    mov   r11, [rbx + 392]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_number_f
.p2align 4
eita_handler_number_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 400]
    mov   r9, [rbx + 408]
    mov   r10, [rbx + 416]
    mov   r11, [rbx + 424]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_gaslimit_f
.p2align 4
eita_handler_gaslimit_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 432]
    mov   r9, [rbx + 440]
    mov   r10, [rbx + 448]
    mov   r11, [rbx + 456]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_basefee_f
.p2align 4
eita_handler_basefee_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 464]
    mov   r9, [rbx + 472]
    mov   r10, [rbx + 480]
    mov   r11, [rbx + 488]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_prevrandao_f
.p2align 4
eita_handler_prevrandao_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    lea   rcx, [rbx + 512]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_blobhash_f
.p2align 4
eita_handler_blobhash_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   .Lbh_zero_f
    mov   rcx, [rbx + 560]
    cmp   r8, rcx
    jae   .Lbh_zero_f
    mov   rdx, [rbx + 552]
    mov   rcx, r8
    shl   rcx, 5
    add   rcx, rdx
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    jmp   .Lbh_done_f
.Lbh_zero_f:
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
.Lbh_done_f:
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_blobbasefee_f
.p2align 4
eita_handler_blobbasefee_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    lea   rcx, [rbx + 568]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_pc_f
.p2align 4
eita_handler_pc_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    lea   r8, [rbp - 1]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_msize_f
.p2align 4
eita_handler_msize_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 48]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_gas_f
.p2align 4
eita_handler_gas_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    sub   r15, 0
    jb    eita_oog
    mov   r8, r15
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    ret

.globl eita_handler_calldatasize_f
.p2align 4
eita_handler_calldatasize_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 88]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_codesize_f
.p2align 4
eita_handler_codesize_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 72]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_returndatasize_f
.p2align 4
eita_handler_returndatasize_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, [rbx + 104]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_sstore_f
.p2align 4
eita_handler_sstore_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 2300
    cmp   r15, rcx
    jbe   eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rbx + 496]
    mov   rax, [rax + 8]
    call  rax
    sub   r15, rax
    jb    eita_oog
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 16]
    mov   rsi, 104
    mov   rax, rdx
    imul  rax, rsi
    add   rax, rdi
    add   rdx, 1
    mov   [rcx + 0], rdx
    mov   qword ptr [rax + 0], 0
    mov   rdx, [rbx + 144]
    mov   rsi, [rbx + 152]
    mov   [rax + 8], rdx
    mov   [rax + 16], rsi
    mov   rdi, [rbx + 160]
    mov   rsi, [rbx + 168]
    mov   [rax + 24], rdi
    mov   [rax + 32], rsi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    mov   [rax + 40], r8
    mov   [rax + 48], r9
    mov   [rax + 56], r10
    mov   [rax + 64], r11
    mov   rcx, [r12 + r13 - 64]
    mov   [rax + 72], rcx
    mov   rcx, [r12 + r13 - 56]
    mov   [rax + 80], rcx
    mov   rcx, [r12 + r13 - 48]
    mov   [rax + 88], rcx
    mov   rcx, [r12 + r13 - 40]
    mov   [rax + 96], rcx
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_slt_f
.p2align 4
eita_handler_slt_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   r8, [r12 + r13 - 64]
    mov   rcx, r9
    sbb   rcx, [r12 + r13 - 56]
    mov   rcx, r10
    sbb   rcx, [r12 + r13 - 48]
    mov   rcx, r11
    sbb   rcx, [r12 + r13 - 40]
    setl  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_sgt_f
.p2align 4
eita_handler_sgt_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    cmp   [r12 + r13 - 64], r8
    mov   rcx, [r12 + r13 - 56]
    sbb   rcx, r9
    mov   rcx, [r12 + r13 - 48]
    sbb   rcx, r10
    mov   rcx, [r12 + r13 - 40]
    sbb   rcx, r11
    setl  r8b
    movzx r8, r8b
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_mul_f
.p2align 4
eita_handler_mul_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_mul]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_div_f
.p2align 4
eita_handler_div_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_div]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_sdiv_f
.p2align 4
eita_handler_sdiv_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_sdiv]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_mod_f
.p2align 4
eita_handler_mod_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_mod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_smod_f
.p2align 4
eita_handler_smod_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_smod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_exp_f
.p2align 4
eita_handler_exp_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 0
    cmp   qword ptr [r12 + r13 - 40], 0
    jz    .Lexp_l2_f
    lzcnt rdx, qword ptr [r12 + r13 - 40]
    mov   rcx, 256
    sub   rcx, rdx
    jmp   .Lexp_charge_f
.Lexp_l2_f:
    cmp   qword ptr [r12 + r13 - 48], 0
    jz    .Lexp_l1_f
    lzcnt rdx, qword ptr [r12 + r13 - 48]
    mov   rcx, 192
    sub   rcx, rdx
    jmp   .Lexp_charge_f
.Lexp_l1_f:
    cmp   qword ptr [r12 + r13 - 56], 0
    jz    .Lexp_l0_f
    lzcnt rdx, qword ptr [r12 + r13 - 56]
    mov   rcx, 128
    sub   rcx, rdx
    jmp   .Lexp_charge_f
.Lexp_l0_f:
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    .Lexp_zero_e_f
    lzcnt rdx, qword ptr [r12 + r13 - 64]
    mov   rcx, 64
    sub   rcx, rdx
.Lexp_charge_f:
    add   rcx, 7
    shr   rcx, 3
    jmp   .Lexp_do_gas_f
.Lexp_zero_e_f:
    mov   rcx, 0
.Lexp_do_gas_f:
    mov   rdx, 50
    imul  rcx, rdx
    add   rcx, 0
    sub   r15, rcx
    jb    eita_oog
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_exp]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_shl_f
.p2align 4
eita_handler_shl_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_shl]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_shr_f
.p2align 4
eita_handler_shr_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_shr]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_sar_f
.p2align 4
eita_handler_sar_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_sar]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_byte_f
.p2align 4
eita_handler_byte_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_byte]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_signextend_f
.p2align 4
eita_handler_signextend_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_signextend]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_addmod_f
.p2align 4
eita_handler_addmod_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_addmod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_mulmod_f
.p2align 4
eita_handler_mulmod_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_mulmod]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_calldataload_f
.p2align 4
eita_handler_calldataload_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    mov   rsi, rbx
    lea   rdx, [r13 - 32]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_calldataload]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_calldatacopy_f
.p2align 4
eita_handler_calldatacopy_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rdi, [rdx + 8]
    mov   rax, [rdx + 16]
    or    rdi, rax
    mov   rax, [rdx + 24]
    or    rdi, rax
    cmp   rdi, 0
    jnz   eita_oog
    mov   rsi, 0
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rcx, 0
    jz    6f
    mov   rdi, r9
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, rcx
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_calldatacopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_codecopy_f
.p2align 4
eita_handler_codecopy_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rdi, [rdx + 8]
    mov   rax, [rdx + 16]
    or    rdi, rax
    mov   rax, [rdx + 24]
    or    rdi, rax
    cmp   rdi, 0
    jnz   eita_oog
    mov   rsi, 0
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rcx, 0
    jz    6f
    mov   rdi, r9
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, rcx
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_codecopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_returndatacopy_f
.p2align 4
eita_handler_returndatacopy_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdx, [rcx + 8]
    mov   rdi, [rcx + 16]
    or    rdx, rdi
    mov   rdi, [rcx + 24]
    or    rdx, rdi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rdx, [rcx + 0]
    add   rdx, [r12 + r13 - 64]
    jc    eita_oog
    mov   rdi, [rbx + 104]
    cmp   rdx, rdi
    ja    eita_oog
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rdi, [rdx + 8]
    mov   rax, [rdx + 16]
    or    rdi, rax
    mov   rax, [rdx + 24]
    or    rdi, rax
    cmp   rdi, 0
    jnz   eita_oog
    mov   rsi, 0
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rcx, 0
    jz    6f
    mov   rdi, r9
    or    rdi, r10
    or    rdi, r11
    cmp   rdi, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, rcx
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_returndatacopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_mcopy_f
.p2align 4
eita_handler_mcopy_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lmcd0_f
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lmcd1_f
.Lmcd0_f:
    mov   rax, 0
.Lmcd1_f:
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 64]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lmcs0_f
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rcx, rsi
    add   rcx, rdi
    jc    eita_oog
    jmp   .Lmcs1_f
.Lmcs0_f:
    mov   rcx, 0
.Lmcs1_f:
    cmp   rax, rcx
    cmovbe rax, rcx
    lea   rcx, [r13 - 96]
    mov   rdx, r12
    add   rdx, rcx
    mov   rcx, [rdx]
    mov   rsi, 0
    lea   rdi, [rcx + 31]
    cmp   rdi, rcx
    jb    eita_oog
    shr   rdi, 5
    lea   rdi, [rdi + rdi*2]
    add   rsi, rdi
    cmp   rax, 0
    jz    6f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
6:
    sub   r15, rsi
    jb    eita_oog
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [r13 - 96]
    add   rcx, r12
    call  qword ptr [rip + Lsym_eita_helper_mcopy]
    sub   r13, 96
    cmp   r13, 32
    jl    7f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
7:
    ret

.globl eita_handler_keccak256_f
.p2align 4
eita_handler_keccak256_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, [r12 + r13 - 64]
    add   rsi, 31
    cmp   rsi, [r12 + r13 - 64]
    jb    eita_oog
    shr   rsi, 5
    lea   rsi, [rsi + rsi*2]
    add   rsi, rsi
    add   rsi, 0
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    sub   r15, rsi
    jb    eita_oog
    sub   rsp, 32
    mov   rdi, rbx
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    lea   rcx, [rsp + 0]
    call  qword ptr [rip + Lsym_eita_helper_keccak256]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_sload_f
.p2align 4
eita_handler_sload_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 0]
    call  rax
    sub   r15, rax
    jb    eita_oog
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_tload_f
.p2align 4
eita_handler_tload_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, 100
    sub   r15, rcx
    jb    eita_oog
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    mov   rdi, [rdi + 64]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [rsp + 0]
    call  qword ptr [rip + Lsym_eita_ts_tload]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_balance_f
.p2align 4
eita_handler_balance_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 32]
    call  rax
    sub   r15, rax
    jb    eita_oog
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_selfbalance_f
.p2align 4
eita_handler_selfbalance_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 32]
    call  rax
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_extcodesize_f
.p2align 4
eita_handler_extcodesize_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 16
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 40]
    call  rax
    mov   rcx, rax
    sub   r15, rcx
    jb    eita_oog
    mov   r8, [rsp + 0]
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   rsp, 16
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_extcodehash_f
.p2align 4
eita_handler_extcodehash_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 48]
    call  rax
    sub   r15, rax
    jb    eita_oog
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_blockhash_f
.p2align 4
eita_handler_blockhash_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rsp, 32
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [rsp + 0]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 64]
    call  rax
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_extcodecopy_f
.p2align 4
eita_handler_extcodecopy_f:
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rdi, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    lea   rcx, [r13 - 64]
    add   rcx, r12
    cmp   rdi, 0
    jz    .Lxcd0_f
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    or    rdx, rsi
    mov   rsi, [rcx + 24]
    or    rdx, rsi
    cmp   rdx, 0
    jnz   eita_oog
    mov   rsi, [rcx + 0]
    mov   rax, rsi
    add   rax, rdi
    jc    eita_oog
    jmp   .Lxcd1_f
.Lxcd0_f:
    mov   rax, 0
.Lxcd1_f:
    mov   rsi, 0
    cmp   rax, 0
    jz    90f
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
90:
    mov   rdi, [rbx + 504]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   r11, [rcx]
    mov   r10, [rbx + 40]
    mov   rdx, r10
    add   rdx, r11
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   r11, [rcx + 8]
    mov   r10, [rcx + 16]
    or    r11, r10
    mov   r10, [rcx + 24]
    or    r11, r10
    mov   rcx, [rcx]
    cmp   r11, 0
    jz    94f
    mov   rcx, 0
    sub   rcx, 1
94:
    lea   r8, [r13 - 128]
    add   r8, r12
    mov   r8, [r8]
    mov   rax, [rbx + 496]
    mov   rax, [rax + 56]
    call  rax
    sub   r15, rax
    jb    eita_oog
    sub   r13, 128
    cmp   r13, 32
    jl    91f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
91:
    ret

.globl eita_handler_mload_f
.p2align 4
eita_handler_mload_f:
    cmp   r13, 32
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, 32
    jc    eita_oog
    mov   rsi, 0
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
    mov   rcx, [rbx + 40]
    lea   rdx, [r8 + 32]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    add   rcx, r8
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    bswap r8
    bswap r9
    bswap r10
    bswap r11
    mov   rcx, r8
    mov   r8, r11
    mov   r11, rcx
    mov   rcx, r9
    mov   r9, r10
    mov   r10, rcx
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    ret

.globl eita_handler_mstore_f
.p2align 4
eita_handler_mstore_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, 32
    jc    eita_oog
    mov   rsi, 0
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
    lea   rdx, [r8 + 32]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    mov   rcx, [rbx + 40]
    add   rcx, r8
    mov   rax, [r12 + r13 - 40]
    bswap rax
    mov   rdx, [r12 + r13 - 48]
    bswap rdx
    mov   rsi, [r12 + r13 - 56]
    bswap rsi
    mov   rdi, [r12 + r13 - 64]
    bswap rdi
    mov   [rcx + 0], rax
    mov   [rcx + 8], rdx
    mov   [rcx + 16], rsi
    mov   [rcx + 24], rdi
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_mstore8_f
.p2align 4
eita_handler_mstore8_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, 1
    jc    eita_oog
    mov   rsi, 0
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
    sub   r15, rsi
    jb    eita_oog
    mov   rcx, [rbx + 40]
    lea   rdx, [r8 + 1]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    mov   rax, [r12 + r13 - 64]
    mov   byte ptr [rcx + r8], al
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_tstore_f
.p2align 4
eita_handler_tstore_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 100
    sub   r15, rcx
    jb    eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rsi, [rbx + 504]
    mov   rdi, [rsi + 64]
    lea   rdx, [rbx + 144]
    lea   rcx, [r13 - 32]
    add   rcx, r12
    lea   r8, [r13 - 64]
    add   r8, r12
    call  qword ptr [rip + Lsym_eita_ts_tstore]
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    ret

.globl eita_handler_push0_f
.p2align 4
eita_handler_push0_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push1_f
.p2align 4
eita_handler_push1_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 56
    add   rbp, 1
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push2_f
.p2align 4
eita_handler_push2_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 48
    add   rbp, 2
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push3_f
.p2align 4
eita_handler_push3_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 40
    add   rbp, 3
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push4_f
.p2align 4
eita_handler_push4_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 32
    add   rbp, 4
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push5_f
.p2align 4
eita_handler_push5_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 24
    add   rbp, 5
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push6_f
.p2align 4
eita_handler_push6_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 16
    add   rbp, 6
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push7_f
.p2align 4
eita_handler_push7_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx]
    bswap r8
    shr   r8, 8
    add   rbp, 7
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push8_f
.p2align 4
eita_handler_push8_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 8
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push9_f
.p2align 4
eita_handler_push9_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 56
    add   rdx, 1
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 9
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push10_f
.p2align 4
eita_handler_push10_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 48
    add   rdx, 2
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 10
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push11_f
.p2align 4
eita_handler_push11_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 40
    add   rdx, 3
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 11
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push12_f
.p2align 4
eita_handler_push12_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 32
    add   rdx, 4
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 12
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push13_f
.p2align 4
eita_handler_push13_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 24
    add   rdx, 5
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 13
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push14_f
.p2align 4
eita_handler_push14_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 16
    add   rdx, 6
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 14
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push15_f
.p2align 4
eita_handler_push15_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx]
    bswap r9
    shr   r9, 8
    add   rdx, 7
    mov   r8, [rdx + 0]
    bswap r8
    add   rbp, 15
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push16_f
.p2align 4
eita_handler_push16_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 16
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push17_f
.p2align 4
eita_handler_push17_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 56
    add   rdx, 1
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 17
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push18_f
.p2align 4
eita_handler_push18_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 48
    add   rdx, 2
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 18
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push19_f
.p2align 4
eita_handler_push19_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 40
    add   rdx, 3
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 19
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push20_f
.p2align 4
eita_handler_push20_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 32
    add   rdx, 4
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 20
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push21_f
.p2align 4
eita_handler_push21_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 24
    add   rdx, 5
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 21
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push22_f
.p2align 4
eita_handler_push22_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 16
    add   rdx, 6
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 22
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push23_f
.p2align 4
eita_handler_push23_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx]
    bswap r10
    shr   r10, 8
    add   rdx, 7
    mov   r9, [rdx + 0]
    bswap r9
    mov   r8, [rdx + 8]
    bswap r8
    add   rbp, 23
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push24_f
.p2align 4
eita_handler_push24_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 24
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push25_f
.p2align 4
eita_handler_push25_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 56
    add   rdx, 1
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 25
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push26_f
.p2align 4
eita_handler_push26_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 48
    add   rdx, 2
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 26
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push27_f
.p2align 4
eita_handler_push27_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 40
    add   rdx, 3
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 27
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push28_f
.p2align 4
eita_handler_push28_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 32
    add   rdx, 4
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 28
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push29_f
.p2align 4
eita_handler_push29_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 24
    add   rdx, 5
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 29
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push30_f
.p2align 4
eita_handler_push30_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 16
    add   rdx, 6
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 30
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push31_f
.p2align 4
eita_handler_push31_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx]
    bswap r11
    shr   r11, 8
    add   rdx, 7
    mov   r10, [rdx + 0]
    bswap r10
    mov   r9, [rdx + 8]
    bswap r9
    mov   r8, [rdx + 16]
    bswap r8
    add   rbp, 31
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_push32_f
.p2align 4
eita_handler_push32_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    mov   r8, 0
    mov   r9, 0
    mov   r10, 0
    mov   r11, 0
    mov   rdx, r14
    add   rdx, rbp
    mov   r11, [rdx + 0]
    bswap r11
    mov   r10, [rdx + 8]
    bswap r10
    mov   r9, [rdx + 16]
    bswap r9
    mov   r8, [rdx + 24]
    bswap r8
    add   rbp, 32
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_log0_f
.p2align 4
eita_handler_log0_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 0
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 64
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 32]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 0]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 0
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log1_f
.p2align 4
eita_handler_log1_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 0
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 96
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 64]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 32]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 1
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log2_f
.p2align 4
eita_handler_log2_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 0
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 128
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 96]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 64]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 2
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log3_f
.p2align 4
eita_handler_log3_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 160
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 0
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 160
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 128]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 96]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 3
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_log4_f
.p2align 4
eita_handler_log4_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rcx, [r12 + r13 - 56]
    or    rcx, [r12 + r13 - 48]
    or    rcx, [r12 + r13 - 40]
    cmp   rcx, 0
    jnz   eita_oog
    mov   rsi, 0
    mov   rax, [r12 + r13 - 64]
    shl   rax, 3
    add   rsi, rax
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    4f
    mov   rcx, r9
    or    rcx, r10
    or    rcx, r11
    cmp   rcx, 0
    jnz   eita_oog
    mov   rax, r8
    add   rax, [r12 + r13 - 64]
    jc    eita_oog
    mov   rcx, [rbx + 56]
    cmp   rax, rcx
    ja    eita_oog
    lea   rcx, [rax + 31]
    shr   rcx, 5
    mov   rdx, [rbx + 48]
    shr   rdx, 5
    cmp   rcx, rdx
    jbe   7f
    mov   rdi, rcx
    imul  rdi, rcx
    shr   rdi, 9
    add   rdi, rcx
    lea   rdi, [rdi + rcx*2]
    mov   rcx, rdx
    imul  rcx, rdx
    shr   rcx, 9
    add   rcx, rdx
    lea   rcx, [rcx + rdx*2]
    sub   rdi, rcx
    add   rsi, rdi
    lea   rcx, [rax + 31]
    shr   rcx, 5
    shl   rcx, 5
    mov   [rbx + 48], rcx
7:
4:
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 8]
    add   rdx, 1
    mov   [rcx + 8], rdx
    mov   rdx, r8
    add   rdx, [r12 + r13 - 64]
    mov   rdi, [rbx + 24]
    cmp   rdx, rdi
    cmova rdi, rdx
    mov   [rbx + 24], rdi
    sub   r13, 192
    sub   r15, rsi
    jb    eita_oog
    mov   rax, [rbx + 496]
    mov   rax, [rax + 72]
    cmp   rax, 0
    jz    7f
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rcx, r12
    add   rcx, r13
    lea   rdx, [r13 + 160]
    add   rdx, r12
    mov   rdx, [rdx]
    mov   r8, [rbx + 40]
    add   r8, rdx
    lea   rdx, [r13 + 128]
    add   rdx, r12
    mov   r9, [rdx]
    mov   rdx, 4
    call  rax
7:
    cmp   r13, 32
    jl    5f
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
5:
    ret

.globl eita_handler_dup1_f
.p2align 4
eita_handler_dup1_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 32
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup2_f
.p2align 4
eita_handler_dup2_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup3_f
.p2align 4
eita_handler_dup3_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup4_f
.p2align 4
eita_handler_dup4_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup5_f
.p2align 4
eita_handler_dup5_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 160
    jb    eita_stack_underflow
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup6_f
.p2align 4
eita_handler_dup6_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup7_f
.p2align 4
eita_handler_dup7_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 224
    jb    eita_stack_underflow
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup8_f
.p2align 4
eita_handler_dup8_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 256
    jb    eita_stack_underflow
    lea   rcx, [r13 - 256]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup9_f
.p2align 4
eita_handler_dup9_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 288
    jb    eita_stack_underflow
    lea   rcx, [r13 - 288]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup10_f
.p2align 4
eita_handler_dup10_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 320
    jb    eita_stack_underflow
    lea   rcx, [r13 - 320]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup11_f
.p2align 4
eita_handler_dup11_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 352
    jb    eita_stack_underflow
    lea   rcx, [r13 - 352]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup12_f
.p2align 4
eita_handler_dup12_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 384
    jb    eita_stack_underflow
    lea   rcx, [r13 - 384]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup13_f
.p2align 4
eita_handler_dup13_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 416
    jb    eita_stack_underflow
    lea   rcx, [r13 - 416]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup14_f
.p2align 4
eita_handler_dup14_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 448
    jb    eita_stack_underflow
    lea   rcx, [r13 - 448]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup15_f
.p2align 4
eita_handler_dup15_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 480
    jb    eita_stack_underflow
    lea   rcx, [r13 - 480]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_dup16_f
.p2align 4
eita_handler_dup16_f:
    cmp   r13, 32768
    jae   eita_stack_overflow
    cmp   r13, 512
    jb    eita_stack_underflow
    lea   rcx, [r13 - 512]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap1_f
.p2align 4
eita_handler_swap1_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap2_f
.p2align 4
eita_handler_swap2_f:
    cmp   r13, 96
    jb    eita_stack_underflow
    lea   rcx, [r13 - 96]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap3_f
.p2align 4
eita_handler_swap3_f:
    cmp   r13, 128
    jb    eita_stack_underflow
    lea   rcx, [r13 - 128]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap4_f
.p2align 4
eita_handler_swap4_f:
    cmp   r13, 160
    jb    eita_stack_underflow
    lea   rcx, [r13 - 160]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap5_f
.p2align 4
eita_handler_swap5_f:
    cmp   r13, 192
    jb    eita_stack_underflow
    lea   rcx, [r13 - 192]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap6_f
.p2align 4
eita_handler_swap6_f:
    cmp   r13, 224
    jb    eita_stack_underflow
    lea   rcx, [r13 - 224]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap7_f
.p2align 4
eita_handler_swap7_f:
    cmp   r13, 256
    jb    eita_stack_underflow
    lea   rcx, [r13 - 256]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap8_f
.p2align 4
eita_handler_swap8_f:
    cmp   r13, 288
    jb    eita_stack_underflow
    lea   rcx, [r13 - 288]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap9_f
.p2align 4
eita_handler_swap9_f:
    cmp   r13, 320
    jb    eita_stack_underflow
    lea   rcx, [r13 - 320]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap10_f
.p2align 4
eita_handler_swap10_f:
    cmp   r13, 352
    jb    eita_stack_underflow
    lea   rcx, [r13 - 352]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap11_f
.p2align 4
eita_handler_swap11_f:
    cmp   r13, 384
    jb    eita_stack_underflow
    lea   rcx, [r13 - 384]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap12_f
.p2align 4
eita_handler_swap12_f:
    cmp   r13, 416
    jb    eita_stack_underflow
    lea   rcx, [r13 - 416]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap13_f
.p2align 4
eita_handler_swap13_f:
    cmp   r13, 448
    jb    eita_stack_underflow
    lea   rcx, [r13 - 448]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap14_f
.p2align 4
eita_handler_swap14_f:
    cmp   r13, 480
    jb    eita_stack_underflow
    lea   rcx, [r13 - 480]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap15_f
.p2align 4
eita_handler_swap15_f:
    cmp   r13, 512
    jb    eita_stack_underflow
    lea   rcx, [r13 - 512]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_swap16_f
.p2align 4
eita_handler_swap16_f:
    cmp   r13, 544
    jb    eita_stack_underflow
    lea   rcx, [r13 - 544]
    add   rcx, r12
    mov   rax, [rcx + 0]
    mov   rdx, [rcx + 8]
    mov   rsi, [rcx + 16]
    mov   rdi, [rcx + 24]
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   r8, rax
    mov   r9, rdx
    mov   r10, rsi
    mov   r11, rdi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    sub   r15, 0
    jb    eita_oog
    ret

.globl eita_handler_sstore_nosentry_f
.p2align 4
eita_handler_sstore_nosentry_f:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rbx + 496]
    mov   rax, [rax + 8]
    call  rax
    sub   r15, rax
    jb    eita_oog
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 16]
    mov   rsi, 104
    mov   rax, rdx
    imul  rax, rsi
    add   rax, rdi
    add   rdx, 1
    mov   [rcx + 0], rdx
    mov   qword ptr [rax + 0], 0
    mov   rdx, [rbx + 144]
    mov   rsi, [rbx + 152]
    mov   [rax + 8], rdx
    mov   [rax + 16], rsi
    mov   rdi, [rbx + 160]
    mov   rsi, [rbx + 168]
    mov   [rax + 24], rdi
    mov   [rax + 32], rsi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    mov   [rax + 40], r8
    mov   [rax + 48], r9
    mov   [rax + 56], r10
    mov   [rax + 64], r11
    mov   rcx, [r12 + r13 - 64]
    mov   [rax + 72], rcx
    mov   rcx, [r12 + r13 - 56]
    mov   [rax + 80], rcx
    mov   rcx, [r12 + r13 - 48]
    mov   [rax + 88], rcx
    mov   rcx, [r12 + r13 - 40]
    mov   [rax + 96], rcx
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_exp_pre160_f
.p2align 4
eita_handler_exp_pre160_f:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 0
    cmp   qword ptr [r12 + r13 - 40], 0
    jz    .Lexp_l2_pre160_f
    lzcnt rdx, qword ptr [r12 + r13 - 40]
    mov   rcx, 256
    sub   rcx, rdx
    jmp   .Lexp_charge_pre160_f
.Lexp_l2_pre160_f:
    cmp   qword ptr [r12 + r13 - 48], 0
    jz    .Lexp_l1_pre160_f
    lzcnt rdx, qword ptr [r12 + r13 - 48]
    mov   rcx, 192
    sub   rcx, rdx
    jmp   .Lexp_charge_pre160_f
.Lexp_l1_pre160_f:
    cmp   qword ptr [r12 + r13 - 56], 0
    jz    .Lexp_l0_pre160_f
    lzcnt rdx, qword ptr [r12 + r13 - 56]
    mov   rcx, 128
    sub   rcx, rdx
    jmp   .Lexp_charge_pre160_f
.Lexp_l0_pre160_f:
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    .Lexp_zero_e_pre160_f
    lzcnt rdx, qword ptr [r12 + r13 - 64]
    mov   rcx, 64
    sub   rcx, rdx
.Lexp_charge_pre160_f:
    add   rcx, 7
    shr   rcx, 3
    jmp   .Lexp_do_gas_pre160_f
.Lexp_zero_e_pre160_f:
    mov   rcx, 0
.Lexp_do_gas_pre160_f:
    mov   rdx, 10
    imul  rcx, rdx
    add   rcx, 0
    sub   r15, rcx
    jb    eita_oog
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_exp]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_exp_pre160
.p2align 4
eita_handler_exp_pre160:
    cmp   r13, 64
    jb    eita_stack_underflow
    mov   rcx, 0
    cmp   qword ptr [r12 + r13 - 40], 0
    jz    .Lexp_l2_pre160
    lzcnt rdx, qword ptr [r12 + r13 - 40]
    mov   rcx, 256
    sub   rcx, rdx
    jmp   .Lexp_charge_pre160
.Lexp_l2_pre160:
    cmp   qword ptr [r12 + r13 - 48], 0
    jz    .Lexp_l1_pre160
    lzcnt rdx, qword ptr [r12 + r13 - 48]
    mov   rcx, 192
    sub   rcx, rdx
    jmp   .Lexp_charge_pre160
.Lexp_l1_pre160:
    cmp   qword ptr [r12 + r13 - 56], 0
    jz    .Lexp_l0_pre160
    lzcnt rdx, qword ptr [r12 + r13 - 56]
    mov   rcx, 128
    sub   rcx, rdx
    jmp   .Lexp_charge_pre160
.Lexp_l0_pre160:
    cmp   qword ptr [r12 + r13 - 64], 0
    jz    .Lexp_zero_e_pre160
    lzcnt rdx, qword ptr [r12 + r13 - 64]
    mov   rcx, 64
    sub   rcx, rdx
.Lexp_charge_pre160:
    add   rcx, 7
    shr   rcx, 3
    jmp   .Lexp_do_gas_pre160
.Lexp_zero_e_pre160:
    mov   rcx, 0
.Lexp_do_gas_pre160:
    mov   rdx, 10
    imul  rcx, rdx
    add   rcx, 10
    sub   r15, rcx
    jb    eita_oog
    sub   rsp, 32
    lea   rdi, [rsp + 0]
    lea   rsi, [r13 - 32]
    add   rsi, r12
    lea   rdx, [r13 - 64]
    add   rdx, r12
    call  qword ptr [rip + Lsym_eita_helper_exp]
    lea   rcx, [rsp + 0]
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    add   rsp, 32
    sub   r13, 32
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_handler_selfdestruct_pre150
.p2align 4
eita_handler_selfdestruct_pre150:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 32
    jb    eita_stack_underflow
    sub   rbp, 1
    mov   rcx, 0
    sub   r15, rcx
    jb    eita_oog
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    mov   rdx, rcx
    mov   rax, [rbx + 496]
    mov   rax, [rax + 104]
    call  rax
    sub   r15, rax
    jb    eita_oog
    mov   rcx, 1
    mov   byte ptr [rbx + 128], cl
    sub   r13, 32
    jmp   eita_sync_and_ret

.globl eita_handler_sstore_nosentry
.p2align 4
eita_handler_sstore_nosentry:
    movzx rcx, byte ptr [rbx + 130]
    cmp   rcx, 0
    jnz   eita_static_violation
    cmp   r13, 64
    jb    eita_stack_underflow
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   [rcx + 0], r8
    mov   [rcx + 8], r9
    mov   [rcx + 16], r10
    mov   [rcx + 24], r11
    mov   rdi, [rbx + 504]
    lea   rsi, [rbx + 144]
    lea   rdx, [r13 - 32]
    add   rdx, r12
    lea   rcx, [r13 - 64]
    add   rcx, r12
    mov   rax, [rbx + 496]
    mov   rax, [rax + 8]
    call  rax
    sub   r15, rax
    jb    eita_oog
    mov   rcx, [rbx + 504]
    mov   rdx, [rcx + 0]
    mov   rdi, [rcx + 16]
    mov   rsi, 104
    mov   rax, rdx
    imul  rax, rsi
    add   rax, rdi
    add   rdx, 1
    mov   [rcx + 0], rdx
    mov   qword ptr [rax + 0], 0
    mov   rdx, [rbx + 144]
    mov   rsi, [rbx + 152]
    mov   [rax + 8], rdx
    mov   [rax + 16], rsi
    mov   rdi, [rbx + 160]
    mov   rsi, [rbx + 168]
    mov   [rax + 24], rdi
    mov   [rax + 32], rsi
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    mov   [rax + 40], r8
    mov   [rax + 48], r9
    mov   [rax + 56], r10
    mov   [rax + 64], r11
    mov   rcx, [r12 + r13 - 64]
    mov   [rax + 72], rcx
    mov   rcx, [r12 + r13 - 56]
    mov   [rax + 80], rcx
    mov   rcx, [r12 + r13 - 48]
    mov   [rax + 88], rcx
    mov   rcx, [r12 + r13 - 40]
    mov   [rax + 96], rcx
    sub   r13, 64
    lea   rcx, [r13 - 32]
    add   rcx, r12
    mov   r8, [rcx + 0]
    mov   r9, [rcx + 8]
    mov   r10, [rcx + 16]
    mov   r11, [rcx + 24]
    lea   rcx, [r13 - 64]
    add   rcx, r12
    ret

.globl eita_set_fork
.p2align 4
eita_set_fork:
    mov   rax, 21
    cmp   rdi, rax
    cmovbe  rax, rdi
    lea   rcx, [rip + eita_fork_tables]
    mov   rax, qword ptr [rcx + rax*8]
    lea   rcx, [rip + eita_dispatch_ptr]
    mov   qword ptr [rcx], rax
    ret

.globl eita_execute_program
.p2align 4
eita_execute_program:
    push  rbx
    push  rbp
    push  r12
    push  r13
    sub   rsp, 8
    mov   rbx, rdi
    mov   r12, rsi
    mov   r13, rdx
    mov   rbp, rcx
Lrp_loop:
    movzx  rax, byte ptr [rbx + 128]
    cmp   rax, 0
    jne   Lrp_halted
    cmp   rbp, 0
    je    Lrp_fuel
    sub   rbp, 1
    mov   rax, qword ptr [rbx]
    cmp   rax, qword ptr [r12]
    jae   Lrp_miss
    mov   rsi, qword ptr [r12 + rax*8 + 8]
    cmp   rsi, 0
    je    Lrp_miss
    mov   rdi, rbx
    call  r13
    jmp   Lrp_loop
Lrp_halted:
    mov   rax, 0
    jmp   Lrp_ret
Lrp_miss:
    mov   rax, 1
    jmp   Lrp_ret
Lrp_fuel:
    mov   rax, 2
Lrp_ret:
    add   rsp, 8
    pop   r13
    pop   r12
    pop   rbp
    pop   rbx
    ret

.globl eita_call_gas
.p2align 4
eita_call_gas:
    mov   rax, 0
    mov   r10, 100
    mov   r9, 2600
    test  rsi, 1
    cmovne  r10, r9
    mov   r9, 9000
    test  rsi, 2
    cmove  r9, rax
    add   r10, r9
    mov   r9, 25000
    test  rsi, 4
    cmove  r9, rax
    add   r10, r9
    add   r10, rdx
    mov   r11, r8
    sub   r11, r10
    cmovb  r11, rax
    mov   r9, r11
    shr   r9, 6
    sub   r11, r9
    cmp   rcx, r11
    cmovb  r11, rcx
    mov   r9, 2300
    test  rsi, 2
    cmove  r9, rax
    mov   [rdi + 0], r10
    mov   [rdi + 8], r11
    mov   [rdi + 16], r9
    ret

.globl eita_call_gas_frontier
.p2align 4
eita_call_gas_frontier:
    mov   rax, 0
    mov   r10, 40
    mov   r9, 9000
    test  rsi, 2
    cmove  r9, rax
    add   r10, r9
    mov   r9, 25000
    test  rsi, 4
    cmove  r9, rax
    add   r10, r9
    mov   r11, rcx
    mov   r9, 2300
    test  rsi, 2
    cmove  r9, rax
    mov   [rdi + 0], r10
    mov   [rdi + 8], r11
    mov   [rdi + 16], r9
    ret

.globl eita_call_gas_tangerine
.p2align 4
eita_call_gas_tangerine:
    mov   rax, 0
    mov   r10, 700
    mov   r9, 9000
    test  rsi, 2
    cmove  r9, rax
    add   r10, r9
    mov   r9, 25000
    test  rsi, 4
    cmove  r9, rax
    add   r10, r9
    mov   r11, r8
    sub   r11, r10
    cmovb  r11, rax
    mov   r9, r11
    shr   r9, 6
    sub   r11, r9
    cmp   rcx, r11
    cmovb  r11, rcx
    mov   r9, 2300
    test  rsi, 2
    cmove  r9, rax
    mov   [rdi + 0], r10
    mov   [rdi + 8], r11
    mov   [rdi + 16], r9
    ret

.globl eita_sstore_gas_legacy
.p2align 4
eita_sstore_gas_legacy:
    mov   r11, 0
    mov   r10, [rcx + 0]
    mov   rax, [rcx + 8]
    or    r10, rax
    mov   rax, [rcx + 16]
    or    r10, rax
    mov   rax, [rcx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 1
    or    r11, r10
    mov   r10, [r8 + 0]
    mov   rax, [r8 + 8]
    or    r10, rax
    mov   rax, [r8 + 16]
    or    r10, rax
    mov   rax, [r8 + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 2
    or    r11, r10
    mov   r10, 5000
    test  r11, 2
    je    1f
    test  r11, 4
    jne   1f
    mov   r10, 20000
1:
    mov   rax, 0
    test  r11, 2
    jne   2f
    test  r11, 4
    je    2f
    mov   rax, 15000
2:
    mov   r9, rsi
    add   r9, rax
    mov   [rdi + 0], r10
    mov   [rdi + 8], r9
    ret

.globl eita_sstore_gas_eip1283
.p2align 4
eita_sstore_gas_eip1283:
    cmp   r9, 0
    sete  r11b
    movzx r11, r11b
    xor   r11, 1
    shl   r11, 6
    mov   r10, [rdx + 0]
    mov   rax, [rdx + 8]
    or    r10, rax
    mov   rax, [rdx + 16]
    or    r10, rax
    mov   rax, [rdx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [rcx + 8]
    or    r10, rax
    mov   rax, [rcx + 16]
    or    r10, rax
    mov   rax, [rcx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 1
    or    r11, r10
    mov   r10, [r8 + 0]
    mov   rax, [r8 + 8]
    or    r10, rax
    mov   rax, [r8 + 16]
    or    r10, rax
    mov   rax, [r8 + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 2
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [rcx + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [rcx + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [rcx + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [rcx + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 3
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rcx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 4
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 5
    or    r11, r10
    mov   rcx, 0
    test  r11, 16
    je    1f
    mov   r10, 200
    mov   r9, rsi
    jmp   9f
1:
    test  r11, 8
    je    2f
    test  r11, 1
    je    3f
    mov   r10, 20000
    mov   r9, rsi
    jmp   9f
3:
    mov   r10, 5000
    mov   rax, 15000
    test  r11, 4
    cmove  rax, rcx
    mov   r9, rsi
    add   r9, rax
    jmp   9f
2:
    mov   r10, 200
    mov   rdx, 0
    test  r11, 1
    jne   4f
    test  r11, 2
    je    5f
    mov   rax, 15000
    sub   rdx, rax
5:
    test  r11, 4
    je    4f
    mov   rax, 15000
    add   rdx, rax
4:
    test  r11, 32
    je    6f
    mov   rax, 4800
    mov   r8, 19800
    test  r11, 1
    cmovne  rax, r8
    add   rdx, rax
6:
    mov   r9, rsi
    add   r9, rdx
    cmp   r9, 0
    cmovl  r9, rcx
9:
    mov   [rdi + 0], r10
    mov   [rdi + 8], r9
    ret

.globl eita_sstore_gas_eip2200
.p2align 4
eita_sstore_gas_eip2200:
    cmp   r9, 0
    sete  r11b
    movzx r11, r11b
    xor   r11, 1
    shl   r11, 6
    mov   r10, [rdx + 0]
    mov   rax, [rdx + 8]
    or    r10, rax
    mov   rax, [rdx + 16]
    or    r10, rax
    mov   rax, [rdx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [rcx + 8]
    or    r10, rax
    mov   rax, [rcx + 16]
    or    r10, rax
    mov   rax, [rcx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 1
    or    r11, r10
    mov   r10, [r8 + 0]
    mov   rax, [r8 + 8]
    or    r10, rax
    mov   rax, [r8 + 16]
    or    r10, rax
    mov   rax, [r8 + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 2
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [rcx + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [rcx + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [rcx + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [rcx + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 3
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rcx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 4
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 5
    or    r11, r10
    mov   rcx, 0
    mov   r10, 800
    mov   r9, rsi
    test  r11, 16
    jne   9f
    test  r11, 8
    je    1f
    mov   rax, 20000
    mov   rdx, 5000
    test  r11, 1
    mov   r10, rdx
    cmovne  r10, rax
1:
    test  r11, 1
    jne   2f
    test  r11, 2
    jne   2f
    test  r11, 4
    je    2f
    mov   rax, 15000
    add   r9, rax
2:
    test  r11, 1
    jne   3f
    test  r11, 2
    je    3f
    mov   rax, 15000
    mov   rdx, r9
    sub   rdx, rax
    mov   r9, rdx
    cmovb  r9, rcx
3:
    test  r11, 32
    je    9f
    mov   rax, 19200
    mov   rdx, 4200
    test  r11, 1
    cmove  rax, rdx
    add   r9, rax
9:
    mov   [rdi + 0], r10
    mov   [rdi + 8], r9
    ret

.globl eita_sstore_gas_berlin
.p2align 4
eita_sstore_gas_berlin:
    cmp   r9, 0
    sete  r11b
    movzx r11, r11b
    xor   r11, 1
    shl   r11, 6
    mov   r10, [rdx + 0]
    mov   rax, [rdx + 8]
    or    r10, rax
    mov   rax, [rdx + 16]
    or    r10, rax
    mov   rax, [rdx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [rcx + 8]
    or    r10, rax
    mov   rax, [rcx + 16]
    or    r10, rax
    mov   rax, [rcx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 1
    or    r11, r10
    mov   r10, [r8 + 0]
    mov   rax, [r8 + 8]
    or    r10, rax
    mov   rax, [r8 + 16]
    or    r10, rax
    mov   rax, [r8 + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 2
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [rcx + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [rcx + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [rcx + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [rcx + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 3
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rcx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 4
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 5
    or    r11, r10
    mov   rcx, 0
    mov   r10, 100
    mov   rdx, 0
    mov   r8, 0
    test  r11, 16
    jne   8f
    test  r11, 8
    je    1f
    mov   rax, 20000
    mov   r9, 2900
    test  r11, 1
    mov   r10, r9
    cmovne  r10, rax
    test  r11, 1
    jne   8f
    test  r11, 4
    je    8f
    mov   rdx, 15000
    jmp   8f
1:
    test  r11, 1
    jne   2f
    test  r11, 2
    je    3f
    mov   r8, 15000
    jmp   2f
3:
    test  r11, 4
    je    2f
    mov   rdx, 15000
2:
    test  r11, 32
    je    8f
    mov   rax, 2800
    mov   r9, 19900
    test  r11, 1
    cmovne  rax, r9
    add   rdx, rax
8:
    test  r11, 64
    je    4f
    mov   rax, 2100
    add   r10, rax
4:
    mov   r9, rsi
    add   r9, rdx
    mov   rax, r9
    sub   rax, r8
    mov   r9, rax
    cmovb  r9, rcx
    mov   [rdi + 0], r10
    mov   [rdi + 8], r9
    ret

.globl eita_sstore_gas_london
.p2align 4
eita_sstore_gas_london:
    cmp   r9, 0
    sete  r11b
    movzx r11, r11b
    xor   r11, 1
    shl   r11, 6
    mov   r10, [rdx + 0]
    mov   rax, [rdx + 8]
    or    r10, rax
    mov   rax, [rdx + 16]
    or    r10, rax
    mov   rax, [rdx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [rcx + 8]
    or    r10, rax
    mov   rax, [rcx + 16]
    or    r10, rax
    mov   rax, [rcx + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 1
    or    r11, r10
    mov   r10, [r8 + 0]
    mov   rax, [r8 + 8]
    or    r10, rax
    mov   rax, [r8 + 16]
    or    r10, rax
    mov   rax, [r8 + 24]
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 2
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [rcx + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [rcx + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [rcx + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [rcx + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 3
    or    r11, r10
    mov   r10, [rcx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rcx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rcx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 4
    or    r11, r10
    mov   r10, [rdx + 0]
    mov   rax, [r8 + 0]
    xor   r10, rax
    mov   rax, [rdx + 8]
    mov   r9, [r8 + 8]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 16]
    mov   r9, [r8 + 16]
    xor   rax, r9
    or    r10, rax
    mov   rax, [rdx + 24]
    mov   r9, [r8 + 24]
    xor   rax, r9
    or    r10, rax
    cmp   r10, 0
    sete  r10b
    movzx r10, r10b
    shl   r10, 5
    or    r11, r10
    mov   rcx, 0
    mov   r10, 100
    mov   rdx, 0
    mov   r8, 0
    test  r11, 16
    jne   8f
    test  r11, 8
    je    1f
    mov   rax, 20000
    mov   r9, 2900
    test  r11, 1
    mov   r10, r9
    cmovne  r10, rax
    test  r11, 1
    jne   8f
    test  r11, 4
    je    8f
    mov   rdx, 4800
    jmp   8f
1:
    test  r11, 1
    jne   2f
    test  r11, 2
    je    3f
    mov   r8, 4800
    jmp   2f
3:
    test  r11, 4
    je    2f
    mov   rdx, 4800
2:
    test  r11, 32
    je    8f
    mov   rax, 2800
    mov   r9, 19900
    test  r11, 1
    cmovne  rax, r9
    add   rdx, rax
8:
    test  r11, 64
    je    4f
    mov   rax, 2100
    add   r10, rax
4:
    mov   r9, rsi
    add   r9, rdx
    mov   rax, r9
    sub   rax, r8
    mov   r9, rax
    cmovb  r9, rcx
    mov   [rdi + 0], r10
    mov   [rdi + 8], r9
    ret

.data
.p2align 3
Lsym_eita_helper_mul:
    .quad   eita_helper_mul
Lsym_eita_helper_div:
    .quad   eita_helper_div
Lsym_eita_helper_sdiv:
    .quad   eita_helper_sdiv
Lsym_eita_helper_mod:
    .quad   eita_helper_mod
Lsym_eita_helper_smod:
    .quad   eita_helper_smod
Lsym_eita_helper_exp:
    .quad   eita_helper_exp
Lsym_eita_helper_shl:
    .quad   eita_helper_shl
Lsym_eita_helper_shr:
    .quad   eita_helper_shr
Lsym_eita_helper_sar:
    .quad   eita_helper_sar
Lsym_eita_helper_byte:
    .quad   eita_helper_byte
Lsym_eita_helper_signextend:
    .quad   eita_helper_signextend
Lsym_eita_helper_addmod:
    .quad   eita_helper_addmod
Lsym_eita_helper_mulmod:
    .quad   eita_helper_mulmod
Lsym_eita_helper_calldataload:
    .quad   eita_helper_calldataload
Lsym_eita_helper_calldatacopy:
    .quad   eita_helper_calldatacopy
Lsym_eita_helper_codecopy:
    .quad   eita_helper_codecopy
Lsym_eita_helper_returndatacopy:
    .quad   eita_helper_returndatacopy
Lsym_eita_helper_mcopy:
    .quad   eita_helper_mcopy
Lsym_eita_helper_keccak256:
    .quad   eita_helper_keccak256
Lsym_eita_ts_tload:
    .quad   eita_ts_tload
Lsym_eita_helper_returndata_to_mem:
    .quad   eita_helper_returndata_to_mem
Lsym_eita_ts_tstore:
    .quad   eita_ts_tstore
.data
.global eita_dispatch_table
.p2align 3
eita_dispatch_table:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_blobhash
    .quad   eita_handler_blobbasefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_tload
    .quad   eita_handler_tstore
    .quad   eita_handler_mcopy
    .quad   eita_handler_push0
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.global eita_dispatch_ptr
.p2align 3
eita_dispatch_ptr:
    .quad   eita_dispatch_table
.data
.global eita_dispatch_table_frontier
.p2align 3
eita_dispatch_table_frontier:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp_pre160
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct_pre150
.data
.global eita_dispatch_table_homestead
.p2align 3
eita_dispatch_table_homestead:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp_pre160
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct_pre150
.data
.global eita_dispatch_table_dao_fork
.p2align 3
eita_dispatch_table_dao_fork:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp_pre160
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct_pre150
.data
.global eita_dispatch_table_tangerine_whistle
.p2align 3
eita_dispatch_table_tangerine_whistle:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp_pre160
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_spurious_dragon
.p2align 3
eita_dispatch_table_spurious_dragon:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_byzantium
.p2align 3
eita_dispatch_table_byzantium:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_invalid
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_constantinople
.p2align 3
eita_dispatch_table_constantinople:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_petersburg
.p2align 3
eita_dispatch_table_petersburg:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore_nosentry
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_istanbul
.p2align 3
eita_dispatch_table_istanbul:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_muir_glacier
.p2align 3
eita_dispatch_table_muir_glacier:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_berlin
.p2align 3
eita_dispatch_table_berlin:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_london
.p2align 3
eita_dispatch_table_london:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_arrow_glacier
.p2align 3
eita_dispatch_table_arrow_glacier:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_gray_glacier
.p2align 3
eita_dispatch_table_gray_glacier:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_paris
.p2align 3
eita_dispatch_table_paris:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_shanghai
.p2align 3
eita_dispatch_table_shanghai:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_push0
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_dispatch_table_osaka
.p2align 3
eita_dispatch_table_osaka:
    .quad   eita_handler_stop
    .quad   eita_handler_add
    .quad   eita_handler_mul
    .quad   eita_handler_sub
    .quad   eita_handler_div
    .quad   eita_handler_sdiv
    .quad   eita_handler_mod
    .quad   eita_handler_smod
    .quad   eita_handler_addmod
    .quad   eita_handler_mulmod
    .quad   eita_handler_exp
    .quad   eita_handler_signextend
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_lt
    .quad   eita_handler_gt
    .quad   eita_handler_slt
    .quad   eita_handler_sgt
    .quad   eita_handler_eq
    .quad   eita_handler_iszero
    .quad   eita_handler_and
    .quad   eita_handler_or
    .quad   eita_handler_xor
    .quad   eita_handler_not
    .quad   eita_handler_byte
    .quad   eita_handler_shl
    .quad   eita_handler_shr
    .quad   eita_handler_sar
    .quad   eita_handler_clz
    .quad   eita_handler_invalid
    .quad   eita_handler_keccak256
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_address
    .quad   eita_handler_balance
    .quad   eita_handler_origin
    .quad   eita_handler_caller
    .quad   eita_handler_callvalue
    .quad   eita_handler_calldataload
    .quad   eita_handler_calldatasize
    .quad   eita_handler_calldatacopy
    .quad   eita_handler_codesize
    .quad   eita_handler_codecopy
    .quad   eita_handler_gasprice
    .quad   eita_handler_extcodesize
    .quad   eita_handler_extcodecopy
    .quad   eita_handler_returndatasize
    .quad   eita_handler_returndatacopy
    .quad   eita_handler_extcodehash
    .quad   eita_handler_blockhash
    .quad   eita_handler_coinbase
    .quad   eita_handler_timestamp
    .quad   eita_handler_number
    .quad   eita_handler_prevrandao
    .quad   eita_handler_gaslimit
    .quad   eita_handler_chainid
    .quad   eita_handler_selfbalance
    .quad   eita_handler_basefee
    .quad   eita_handler_blobhash
    .quad   eita_handler_blobbasefee
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_pop
    .quad   eita_handler_mload
    .quad   eita_handler_mstore
    .quad   eita_handler_mstore8
    .quad   eita_handler_sload
    .quad   eita_handler_sstore
    .quad   eita_handler_jump
    .quad   eita_handler_jumpi
    .quad   eita_handler_pc
    .quad   eita_handler_msize
    .quad   eita_handler_gas
    .quad   eita_handler_jumpdest
    .quad   eita_handler_tload
    .quad   eita_handler_tstore
    .quad   eita_handler_mcopy
    .quad   eita_handler_push0
    .quad   eita_handler_push1
    .quad   eita_handler_push2
    .quad   eita_handler_push3
    .quad   eita_handler_push4
    .quad   eita_handler_push5
    .quad   eita_handler_push6
    .quad   eita_handler_push7
    .quad   eita_handler_push8
    .quad   eita_handler_push9
    .quad   eita_handler_push10
    .quad   eita_handler_push11
    .quad   eita_handler_push12
    .quad   eita_handler_push13
    .quad   eita_handler_push14
    .quad   eita_handler_push15
    .quad   eita_handler_push16
    .quad   eita_handler_push17
    .quad   eita_handler_push18
    .quad   eita_handler_push19
    .quad   eita_handler_push20
    .quad   eita_handler_push21
    .quad   eita_handler_push22
    .quad   eita_handler_push23
    .quad   eita_handler_push24
    .quad   eita_handler_push25
    .quad   eita_handler_push26
    .quad   eita_handler_push27
    .quad   eita_handler_push28
    .quad   eita_handler_push29
    .quad   eita_handler_push30
    .quad   eita_handler_push31
    .quad   eita_handler_push32
    .quad   eita_handler_dup1
    .quad   eita_handler_dup2
    .quad   eita_handler_dup3
    .quad   eita_handler_dup4
    .quad   eita_handler_dup5
    .quad   eita_handler_dup6
    .quad   eita_handler_dup7
    .quad   eita_handler_dup8
    .quad   eita_handler_dup9
    .quad   eita_handler_dup10
    .quad   eita_handler_dup11
    .quad   eita_handler_dup12
    .quad   eita_handler_dup13
    .quad   eita_handler_dup14
    .quad   eita_handler_dup15
    .quad   eita_handler_dup16
    .quad   eita_handler_swap1
    .quad   eita_handler_swap2
    .quad   eita_handler_swap3
    .quad   eita_handler_swap4
    .quad   eita_handler_swap5
    .quad   eita_handler_swap6
    .quad   eita_handler_swap7
    .quad   eita_handler_swap8
    .quad   eita_handler_swap9
    .quad   eita_handler_swap10
    .quad   eita_handler_swap11
    .quad   eita_handler_swap12
    .quad   eita_handler_swap13
    .quad   eita_handler_swap14
    .quad   eita_handler_swap15
    .quad   eita_handler_swap16
    .quad   eita_handler_log0
    .quad   eita_handler_log1
    .quad   eita_handler_log2
    .quad   eita_handler_log3
    .quad   eita_handler_log4
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_create
    .quad   eita_handler_call
    .quad   eita_handler_callcode
    .quad   eita_handler_return
    .quad   eita_handler_delegatecall
    .quad   eita_handler_create2
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_staticcall
    .quad   eita_handler_invalid
    .quad   eita_handler_invalid
    .quad   eita_handler_revert
    .quad   eita_handler_invalid
    .quad   eita_handler_selfdestruct
.data
.global eita_fork_tables
.p2align 3
eita_fork_tables:
    .quad   eita_dispatch_table_frontier
    .quad   eita_dispatch_table_homestead
    .quad   eita_dispatch_table_dao_fork
    .quad   eita_dispatch_table_tangerine_whistle
    .quad   eita_dispatch_table_spurious_dragon
    .quad   eita_dispatch_table_byzantium
    .quad   eita_dispatch_table_constantinople
    .quad   eita_dispatch_table_petersburg
    .quad   eita_dispatch_table_istanbul
    .quad   eita_dispatch_table_muir_glacier
    .quad   eita_dispatch_table_berlin
    .quad   eita_dispatch_table_london
    .quad   eita_dispatch_table_arrow_glacier
    .quad   eita_dispatch_table_gray_glacier
    .quad   eita_dispatch_table_paris
    .quad   eita_dispatch_table_shanghai
    .quad   eita_dispatch_table
    .quad   eita_dispatch_table
    .quad   eita_dispatch_table_osaka
    .quad   eita_dispatch_table_osaka
    .quad   eita_dispatch_table_osaka
    .quad   eita_dispatch_table_osaka
.data
.global eita_access_costs
.p2align 3
eita_access_costs:
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
.protected eita_run_one
.protected eita_run
.protected eita_sync_and_ret
.protected eita_invalid_jump
.protected eita_set_fork
.protected eita_execute_program
.protected eita_dispatch_table
.protected eita_dispatch_ptr
.protected eita_fork_tables
.protected eita_access_costs
.protected eita_dispatch_table_osaka
.protected eita_oog
.protected eita_stack_overflow
.protected eita_stack_underflow
.protected eita_static_violation
.protected eita_call_gas
.protected eita_call_gas_frontier
.protected eita_call_gas_tangerine
.protected eita_sstore_gas_legacy
.protected eita_sstore_gas_eip1283
.protected eita_sstore_gas_eip2200
.protected eita_sstore_gas_berlin
.protected eita_sstore_gas_london
.protected eita_handler_add
.protected eita_handler_sub
.protected eita_handler_and
.protected eita_handler_or
.protected eita_handler_xor
.protected eita_handler_lt
.protected eita_handler_gt
.protected eita_handler_eq
.protected eita_handler_iszero
.protected eita_handler_clz
.protected eita_handler_not
.protected eita_handler_pop
.protected eita_handler_stop
.protected eita_handler_jumpdest
.protected eita_handler_invalid
.protected eita_handler_address
.protected eita_handler_origin
.protected eita_handler_caller
.protected eita_handler_coinbase
.protected eita_handler_callvalue
.protected eita_handler_gasprice
.protected eita_handler_chainid
.protected eita_handler_timestamp
.protected eita_handler_number
.protected eita_handler_gaslimit
.protected eita_handler_basefee
.protected eita_handler_prevrandao
.protected eita_handler_blobhash
.protected eita_handler_blobbasefee
.protected eita_handler_pc
.protected eita_handler_msize
.protected eita_handler_gas
.protected eita_handler_calldatasize
.protected eita_handler_codesize
.protected eita_handler_returndatasize
.protected eita_handler_sstore
.protected eita_handler_slt
.protected eita_handler_sgt
.protected eita_handler_mul
.protected eita_handler_div
.protected eita_handler_sdiv
.protected eita_handler_mod
.protected eita_handler_smod
.protected eita_handler_exp
.protected eita_handler_shl
.protected eita_handler_shr
.protected eita_handler_sar
.protected eita_handler_byte
.protected eita_handler_signextend
.protected eita_handler_addmod
.protected eita_handler_mulmod
.protected eita_handler_calldataload
.protected eita_handler_calldatacopy
.protected eita_handler_codecopy
.protected eita_handler_returndatacopy
.protected eita_handler_mcopy
.protected eita_handler_keccak256
.protected eita_handler_sload
.protected eita_handler_tload
.protected eita_handler_balance
.protected eita_handler_selfbalance
.protected eita_handler_extcodesize
.protected eita_handler_extcodehash
.protected eita_handler_blockhash
.protected eita_handler_extcodecopy
.protected eita_handler_staticcall
.protected eita_handler_call
.protected eita_handler_callcode
.protected eita_handler_delegatecall
.protected eita_handler_create
.protected eita_handler_create2
.protected eita_handler_selfdestruct
.protected eita_handler_mload
.protected eita_handler_mstore
.protected eita_handler_mstore8
.protected eita_handler_return
.protected eita_handler_revert
.protected eita_handler_jump
.protected eita_handler_jumpi
.protected eita_handler_tstore
.protected eita_handler_push0
.protected eita_handler_push1
.protected eita_handler_push2
.protected eita_handler_push3
.protected eita_handler_push4
.protected eita_handler_push5
.protected eita_handler_push6
.protected eita_handler_push7
.protected eita_handler_push8
.protected eita_handler_push9
.protected eita_handler_push10
.protected eita_handler_push11
.protected eita_handler_push12
.protected eita_handler_push13
.protected eita_handler_push14
.protected eita_handler_push15
.protected eita_handler_push16
.protected eita_handler_push17
.protected eita_handler_push18
.protected eita_handler_push19
.protected eita_handler_push20
.protected eita_handler_push21
.protected eita_handler_push22
.protected eita_handler_push23
.protected eita_handler_push24
.protected eita_handler_push25
.protected eita_handler_push26
.protected eita_handler_push27
.protected eita_handler_push28
.protected eita_handler_push29
.protected eita_handler_push30
.protected eita_handler_push31
.protected eita_handler_push32
.protected eita_handler_log0
.protected eita_handler_log1
.protected eita_handler_log2
.protected eita_handler_log3
.protected eita_handler_log4
.protected eita_handler_dup1
.protected eita_handler_dup2
.protected eita_handler_dup3
.protected eita_handler_dup4
.protected eita_handler_dup5
.protected eita_handler_dup6
.protected eita_handler_dup7
.protected eita_handler_dup8
.protected eita_handler_dup9
.protected eita_handler_dup10
.protected eita_handler_dup11
.protected eita_handler_dup12
.protected eita_handler_dup13
.protected eita_handler_dup14
.protected eita_handler_dup15
.protected eita_handler_dup16
.protected eita_handler_swap1
.protected eita_handler_swap2
.protected eita_handler_swap3
.protected eita_handler_swap4
.protected eita_handler_swap5
.protected eita_handler_swap6
.protected eita_handler_swap7
.protected eita_handler_swap8
.protected eita_handler_swap9
.protected eita_handler_swap10
.protected eita_handler_swap11
.protected eita_handler_swap12
.protected eita_handler_swap13
.protected eita_handler_swap14
.protected eita_handler_swap15
.protected eita_handler_swap16
.protected eita_handler_add_f
.protected eita_handler_sub_f
.protected eita_handler_and_f
.protected eita_handler_or_f
.protected eita_handler_xor_f
.protected eita_handler_lt_f
.protected eita_handler_gt_f
.protected eita_handler_eq_f
.protected eita_handler_iszero_f
.protected eita_handler_clz_f
.protected eita_handler_not_f
.protected eita_handler_pop_f
.protected eita_handler_jumpdest_f
.protected eita_handler_address_f
.protected eita_handler_origin_f
.protected eita_handler_caller_f
.protected eita_handler_coinbase_f
.protected eita_handler_callvalue_f
.protected eita_handler_gasprice_f
.protected eita_handler_chainid_f
.protected eita_handler_timestamp_f
.protected eita_handler_number_f
.protected eita_handler_gaslimit_f
.protected eita_handler_basefee_f
.protected eita_handler_prevrandao_f
.protected eita_handler_blobhash_f
.protected eita_handler_blobbasefee_f
.protected eita_handler_pc_f
.protected eita_handler_msize_f
.protected eita_handler_gas_f
.protected eita_handler_calldatasize_f
.protected eita_handler_codesize_f
.protected eita_handler_returndatasize_f
.protected eita_handler_sstore_f
.protected eita_handler_slt_f
.protected eita_handler_sgt_f
.protected eita_handler_mul_f
.protected eita_handler_div_f
.protected eita_handler_sdiv_f
.protected eita_handler_mod_f
.protected eita_handler_smod_f
.protected eita_handler_exp_f
.protected eita_handler_shl_f
.protected eita_handler_shr_f
.protected eita_handler_sar_f
.protected eita_handler_byte_f
.protected eita_handler_signextend_f
.protected eita_handler_addmod_f
.protected eita_handler_mulmod_f
.protected eita_handler_calldataload_f
.protected eita_handler_calldatacopy_f
.protected eita_handler_codecopy_f
.protected eita_handler_returndatacopy_f
.protected eita_handler_mcopy_f
.protected eita_handler_keccak256_f
.protected eita_handler_sload_f
.protected eita_handler_tload_f
.protected eita_handler_balance_f
.protected eita_handler_selfbalance_f
.protected eita_handler_extcodesize_f
.protected eita_handler_extcodehash_f
.protected eita_handler_blockhash_f
.protected eita_handler_extcodecopy_f
.protected eita_handler_mload_f
.protected eita_handler_mstore_f
.protected eita_handler_mstore8_f
.protected eita_handler_tstore_f
.protected eita_handler_push0_f
.protected eita_handler_push1_f
.protected eita_handler_push2_f
.protected eita_handler_push3_f
.protected eita_handler_push4_f
.protected eita_handler_push5_f
.protected eita_handler_push6_f
.protected eita_handler_push7_f
.protected eita_handler_push8_f
.protected eita_handler_push9_f
.protected eita_handler_push10_f
.protected eita_handler_push11_f
.protected eita_handler_push12_f
.protected eita_handler_push13_f
.protected eita_handler_push14_f
.protected eita_handler_push15_f
.protected eita_handler_push16_f
.protected eita_handler_push17_f
.protected eita_handler_push18_f
.protected eita_handler_push19_f
.protected eita_handler_push20_f
.protected eita_handler_push21_f
.protected eita_handler_push22_f
.protected eita_handler_push23_f
.protected eita_handler_push24_f
.protected eita_handler_push25_f
.protected eita_handler_push26_f
.protected eita_handler_push27_f
.protected eita_handler_push28_f
.protected eita_handler_push29_f
.protected eita_handler_push30_f
.protected eita_handler_push31_f
.protected eita_handler_push32_f
.protected eita_handler_log0_f
.protected eita_handler_log1_f
.protected eita_handler_log2_f
.protected eita_handler_log3_f
.protected eita_handler_log4_f
.protected eita_handler_dup1_f
.protected eita_handler_dup2_f
.protected eita_handler_dup3_f
.protected eita_handler_dup4_f
.protected eita_handler_dup5_f
.protected eita_handler_dup6_f
.protected eita_handler_dup7_f
.protected eita_handler_dup8_f
.protected eita_handler_dup9_f
.protected eita_handler_dup10_f
.protected eita_handler_dup11_f
.protected eita_handler_dup12_f
.protected eita_handler_dup13_f
.protected eita_handler_dup14_f
.protected eita_handler_dup15_f
.protected eita_handler_dup16_f
.protected eita_handler_swap1_f
.protected eita_handler_swap2_f
.protected eita_handler_swap3_f
.protected eita_handler_swap4_f
.protected eita_handler_swap5_f
.protected eita_handler_swap6_f
.protected eita_handler_swap7_f
.protected eita_handler_swap8_f
.protected eita_handler_swap9_f
.protected eita_handler_swap10_f
.protected eita_handler_swap11_f
.protected eita_handler_swap12_f
.protected eita_handler_swap13_f
.protected eita_handler_swap14_f
.protected eita_handler_swap15_f
.protected eita_handler_swap16_f
.protected eita_handler_sstore_nosentry_f
.protected eita_handler_exp_pre160_f
.protected eita_handler_exp_pre160
.protected eita_handler_selfdestruct_pre150
.protected eita_handler_sstore_nosentry
.protected eita_dispatch_table_frontier
.protected eita_dispatch_table_homestead
.protected eita_dispatch_table_dao_fork
.protected eita_dispatch_table_tangerine_whistle
.protected eita_dispatch_table_spurious_dragon
.protected eita_dispatch_table_byzantium
.protected eita_dispatch_table_constantinople
.protected eita_dispatch_table_petersburg
.protected eita_dispatch_table_istanbul
.protected eita_dispatch_table_muir_glacier
.protected eita_dispatch_table_berlin
.protected eita_dispatch_table_london
.protected eita_dispatch_table_arrow_glacier
.protected eita_dispatch_table_gray_glacier
.protected eita_dispatch_table_paris
.protected eita_dispatch_table_shanghai
.section .note.GNU-stack,"",@progbits
