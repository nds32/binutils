DEFAULT_TEXT_START_ADDR=0
DEFAULT_STACK_START_ADDR=0
MACHINE=
SCRIPT_NAME=nds32elf
TEMPLATE_NAME=elf32
EXTRA_EM_FILE=nds32elf
BIG_OUTPUT_FORMAT="elf32-nds32be"
LITTLE_OUTPUT_FORMAT="elf32-nds32le"
OUTPUT_FORMAT="$LITTLE_OUTPUT_FORMAT"
if [ "${DEFAULT_TEXT_START_ADDR}" = "0" ]; then
    TEXT_START_ADDR=0x500000
else
    TEXT_START_ADDR=${DEFAULT_TEXT_START_ADDR}
fi
ARCH=nds32
MACHINE=
MAXPAGESIZE=0x20
EMBEDDED=yes
COMMONPAGESIZE=0x20

# This sets the stack to the top of simulator memory (32MB).
#OTHER_END_SYMBOLS='PROVIDE (_stack = 0x2000000);'
# This sets the stack to the top of simulator memory (8MB).
#OTHER_END_SYMBOLS='PROVIDE (_stack = 0x800000);'
# This sets the stack to the top of simulator memory (48MB).

if [ "${DEFAULT_STACK_START_ADDR}" = "0" ]; then
    OTHER_END_SYMBOLS='PROVIDE (_stack = 0x3000000);'
else
    OTHER_END_SYMBOLS="PROVIDE (_stack = ${DEFAULT_STACK_START_ADDR});"
fi

# Instruct genscripts.sh not to compile scripts in by COMPILE_IN
# in order to use external linker scripts files.
EMULATION_LIBPATH=
