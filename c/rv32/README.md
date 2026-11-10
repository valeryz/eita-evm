# The rv32 freestanding build

The engine's C compiles for `rv32imac` with `-ffreestanding`, which is what a
Xous (or any bare-metal) target wants and what Homebrew's `riscv64-elf-gcc`
gives you — it ships no newlib, so there are no `<string.h>`, `<stdlib.h>` or
`<stdio.h>` to include.

`include/` is the smallest set of declarations the engine's sources actually
reference — eleven names, measured rather than guessed:

    memcpy memset memcmp   malloc calloc realloc free   abort   stderr fputs fprintf

`shim.c` implements the memory ones and forwards the rest to **host hooks**, so
the engine's C owns no heap and no console of its own:

| hook | who provides it | why |
|---|---|---|
| `eita_rv32_malloc/realloc/free` | the firmware (Rust, on Xous) | one allocator for the whole image; the engine must not bring its own |
| `eita_rv32_abort` | the firmware | `noreturn`; on a signing device this is a refusal, not a crash |
| `eita_rv32_log` | the firmware | the loud-stop paths (`tx_state.c`, `storage_host.c`) |

**`fprintf` does not format.** It logs its format string and drops the
arguments. Every call site is an abort path where the string identifies the
failure, and a varargs formatter is not something this layer should carry; the
alternative — pretending to format — would be worse than saying so here.
