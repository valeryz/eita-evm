/* runtime.c — the host side of the engine, for qemu-system-riscv32 `virt`.
 *
 * The rv32 engine asks its host for six things (c/rv32/README.md): an
 * allocator, abort, and a log sink. On the chip those come from the Xous
 * application; here they come from 1 MiB of static arena and the virt
 * machine's 16550 UART. Nothing else differs, which is the point: the SAME
 * handlers-rv32.S and the same c/rv32/selftest.c run in both places, so a
 * failure here is a failure there.
 *
 * Why this harness exists: before it, the rv32 assembly had never executed
 * anywhere. The host self-test links the ARM64 engine, so it proves the test
 * right, not the lowering. A misaligned 64-bit load in the PUSH handlers got
 * all the way to silicon undetected because of that gap.
 */
#include <stdint.h>
#include <stddef.h>

#define UART0 0x10000000u
#define UART_THR 0u
#define UART_LSR 5u
#define LSR_THRE 0x20u

static void putc_(char c) {
    volatile uint8_t *u = (volatile uint8_t *)UART0;
    while (!(u[UART_LSR] & LSR_THRE)) { }
    u[UART_THR] = (uint8_t)c;
}

static void puts_(const char *s) { while (*s) { if (*s == '\n') putc_('\r'); putc_(*s++); } }

static void putu_(uint64_t v) {
    char b[21]; int i = 0;
    if (!v) { putc_('0'); return; }
    while (v) { b[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i) putc_(b[--i]);
}

static void puthex_(uint32_t v, int digits) {
    puts_("0x");
    for (int i = digits - 1; i >= 0; i--)
        putc_("0123456789abcdef"[(v >> (4 * i)) & 0xf]);
}

/* --- the six host hooks -------------------------------------------------- */

extern char __heap_start[], __heap_end[];
static char *heap_next;

void *eita_rv32_malloc(size_t n) {
    if (!heap_next) heap_next = __heap_start;
    n = (n + 15u) & ~(size_t)15u;
    if (heap_next + n > __heap_end) return 0;
    void *p = heap_next; heap_next += n; return p;
}
/* Bump allocation: `free` is a no-op and `realloc` always moves. The engine's
   allocations in a self-test are few and short-lived. */
void eita_rv32_free(void *p) { (void)p; }
void *eita_rv32_realloc(void *p, size_t n) {
    void *q = eita_rv32_malloc(n);
    if (q && p) { const char *s = p; char *d = q; for (size_t i = 0; i < n; i++) d[i] = s[i]; }
    return q;
}

void _halt_fail(void) __attribute__((noreturn));

void eita_rv32_abort(const char *why) {
    puts_("\nABORT: "); puts_(why ? why : "(null)"); puts_("\n");
    _halt_fail();
}
void eita_rv32_log(const char *msg) { puts_(msg); }
void eita_spec_overflow(const char *where_) {
    puts_("\nSPEC OVERFLOW in "); puts_(where_ ? where_ : "(null)"); puts_("\n");
    _halt_fail();
}

/* --- the trap report, which is the whole reason for a trap vector --------- */

static const char *cause_name(uint32_t c) {
    switch (c) {
    case 0:  return "instruction address misaligned";
    case 1:  return "instruction access fault";
    case 2:  return "illegal instruction";
    case 3:  return "breakpoint";
    case 4:  return "LOAD ADDRESS MISALIGNED";
    case 5:  return "load access fault";
    case 6:  return "STORE ADDRESS MISALIGNED";
    case 7:  return "store access fault";
    default: return "(other)";
    }
}

void qemu_report_trap(uint32_t mcause, uint32_t mepc, uint32_t mtval) {
    puts_("\n*** TRAP: ");
    puts_(cause_name(mcause));
    puts_("  mcause="); puthex_(mcause, 8);
    puts_(" mepc=");    puthex_(mepc, 8);
    puts_(" mtval=");   puthex_(mtval, 8);
    puts_("\n*** (mepc is an address in handlers-rv32.S; "
          "riscv64-elf-addr2line, or nm, says which handler)\n");
}

/* --- the test ------------------------------------------------------------ */

uint32_t eita_selftest(uint64_t *gas_add_out);

/* The names come from the engine's own table (rv32/selftest.c): a second copy
   here printed ten lines after the mask grew to fifteen. */
const char *eita_selftest_check(unsigned i);

void qemu_main(void) {
    puts_("eita: rv32 engine self-test (qemu-system-riscv32 virt)\n");
    uint64_t gas = 0;
    uint32_t bad = eita_selftest(&gas);
    for (unsigned i = 0; eita_selftest_check(i); i++) {
        puts_("eita:   ");
        int n = 0;
        for (const char *q = eita_selftest_check(i); *q; q++) { putc_(*q); n++; }
        while (n++ < 14) putc_(' ');
        puts_((bad & (1u << i)) ? "FAIL\n" : "ok\n");
    }
    if (!bad) { puts_("eita: SELFTEST PASS (ADD program gas_used = "); putu_(gas); puts_(")\n"); }
    else      { puts_("eita: SELFTEST FAIL mask="); puthex_(bad, 2);
                puts_(" (gas_used = "); putu_(gas); puts_(")\n"); }
}
