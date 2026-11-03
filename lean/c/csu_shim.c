/* csu_shim.c — supply __libc_csu_init / __libc_csu_fini on Linux/glibc >= 2.34.
 *
 * The Lean v4.29.1 Linux toolchains (aarch64 AND x86_64) are internally
 * inconsistent, as v4.28.0's were: the bundled `lib/Scrt1.o` is the
 * pre-2.34 crt that calls __libc_csu_init / __libc_csu_fini (passed to
 * __libc_start_main as the `init`/`fini` args), but the linked glibc is
 * >= 2.34 — Ubuntu 24.04 ships 2.39, Amazon Linux 2023 ships 2.34 — which
 * DROPPED those two symbols (the new crt runs .init_array inside
 * __libc_start_main instead). Result: every `lean_exe` fails to link with
 * "undefined symbol: __libc_csu_init / __libc_csu_fini". Reproduced in a
 * clean Ubuntu 24.04 container on the first exe link (emitHostCL), and on
 * GitHub Actions ubuntu-26.04 (glibc 2.43).
 *
 * (A v4.29.1 upgrade once deleted this file after a tarball check "found
 * zero csu_* references" — that check was wrong: nm lists them as
 * UNDEFINED (`U __libc_csu_init`), so the grep must cover undefined
 * symbols, e.g. `nm Scrt1.o | grep -c libc_csu` without --defined-only.)
 *
 * We reconstruct the canonical pre-2.34 implementation. __libc_start_main
 * still honors a non-NULL `init` arg for backward compatibility (it calls
 * it and does NOT independently run .init_array on that path), so running
 * the arrays here is correct and does not double-init. Built into libevmc,
 * so it satisfies the Scrt1.o references in every executable. On glibc
 * <= 2.33 the real definitions win (they're in libc.so, a dynamic dep,
 * which overrides the archive). No-op on macOS (the symbols don't exist
 * there and aren't referenced) — the whole TU is #ifdef'd to __linux__.
 */
#ifdef __linux__
#include <stddef.h>

typedef void (*csu_init_fn)(int, char **, char **);
typedef void (*csu_fini_fn)(void);

/* The linker always materializes these bounds for the .init_array /
 * .fini_array sections; weak keeps it sound even for an empty array. */
extern csu_init_fn __init_array_start[] __attribute__((weak));
extern csu_init_fn __init_array_end[] __attribute__((weak));
extern csu_fini_fn __fini_array_start[] __attribute__((weak));
extern csu_fini_fn __fini_array_end[] __attribute__((weak));

void __libc_csu_init(int argc, char **argv, char **envp) {
  const size_t n = (size_t)(__init_array_end - __init_array_start);
  for (size_t i = 0; i < n; i++)
    __init_array_start[i](argc, argv, envp);
}

void __libc_csu_fini(void) {
  size_t n = (size_t)(__fini_array_end - __fini_array_start);
  /* .fini_array runs in reverse registration order. */
  while (n-- > 0)
    __fini_array_start[n]();
}
#endif /* __linux__ */
