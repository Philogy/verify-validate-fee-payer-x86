// The machine every test vector starts from, unless the vector overrides it.
// lean/X86Test/Harness.lean and gen.py define the same; keep them in sync.

#define PAGE_BYTES 4096
#define CODE_PAGE 0x40000000ull       // r-x; the page after it is unmapped
#define DATA_PAGE 0x50000000ull       // rw-
#define READ_ONLY_PAGE 0x50001000ull  // r--; the page after it is unmapped
#define STACK_PAGE 0x60000000ull      // rw-

#define DEFAULT_AT 0x800  // offset of the instruction in the code page
#define CODE_FILL 0xcc
#define DEFAULT_MXCSR 0x1f80
#define FLAG_LETTERS "CPAZSO"

// Distinct values everywhere, so that reading the wrong byte or register
// shows up as a wrong result.
static inline uint8_t fill_byte(uint64_t address) {
  return (uint8_t)((address * 0x9e3779b97f4a7c15ull) >> 56);
}

static inline uint64_t default_gpr(int i) {
  return i == 4 ? STACK_PAGE + 0x800 : 0x0101010101010101ull * (uint64_t)(i + 1);
}

static inline unsigned __int128 default_xmm(int i) {
  unsigned __int128 v = 0;
  for (int b = 0; b < 16; b++) v = v << 8 | (unsigned)(0xa0 + i);
  return v;
}
