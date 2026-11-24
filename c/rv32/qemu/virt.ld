/* virt.ld — qemu-system-riscv32 `virt` machine, started with `-bios none`, so
   execution begins in M-mode at the base of RAM. */
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M }
SECTIONS {
  .text : { *(.text.init) *(.text .text.*) } > RAM
  .rodata : { *(.rodata .rodata.*) *(.srodata .srodata.*) } > RAM
  .data : {
    __global_pointer$ = . + 0x800;
    *(.data .data.*) *(.sdata .sdata.*)
  } > RAM
  .bss (NOLOAD) : {
    __bss_start = .;
    *(.bss .bss.*) *(.sbss .sbss.*) *(COMMON)
    __bss_end = .;
  } > RAM
  . = ALIGN(16);
  __heap_start = .;
  . = . + 1M;
  __heap_end = .;
  . = ALIGN(16);
  . = . + 256K;
  __stack_top = .;
  . = . + 16K;
  __trap_stack_top = .;
}
