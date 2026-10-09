// Runs each test vector's instruction once on this CPU and prints what
// changed, in the format the Lean runner prints for the model.
//
//   oracle < vectors/foo.txt > expected/foo.txt
//
// Each vector runs in a fresh child process that maps the fixed layout
// (see layout.h), stops, and is single-stepped by the parent with ptrace.
// Must run on a real x86-64 CPU: an emulator's undefined flags, fault
// addresses and float corner cases are exactly what is under test.

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <unistd.h>

#include "layout.h"

static void die(const char *what) {
  perror(what);
  exit(2);
}

struct page {
  uint64_t base;
  int prot;
};

static const struct page pages[] = {
    {CODE_PAGE, PROT_READ | PROT_EXEC},
    {DATA_PAGE, PROT_READ | PROT_WRITE},
    {READ_ONLY_PAGE, PROT_READ},
    {STACK_PAGE, PROT_READ | PROT_WRITE},
};
#define PAGE_COUNT (sizeof pages / sizeof pages[0])

struct vector {
  char hex[64];
  uint8_t code[16];
  int code_len;
  uint64_t at;
  uint64_t gpr[16];
  unsigned __int128 xmm[16];
  char flags[7];  // initial flags, in FLAG_LETTERS order, as 'C' or '-'
  uint32_t mxcsr;
  uint8_t memory[PAGE_COUNT][PAGE_BYTES];
};

struct machine {
  uint64_t rip;
  uint64_t gpr[16];
  uint64_t rflags;
  unsigned __int128 xmm[16];
  uint32_t mxcsr;
  uint8_t memory[PAGE_COUNT][PAGE_BYTES];
};

static const char *gpr_names[16] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
                                    "r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15"};
static const int flag_bits[6] = {0, 2, 4, 6, 7, 11};  // C P A Z S O

static int hex_digit(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static int parse_bytes(const char *s, uint8_t *out, int max) {
  int n = 0;
  while (hex_digit(s[0]) >= 0 && hex_digit(s[1]) >= 0) {
    if (n == max) return -1;
    out[n++] = (uint8_t)(hex_digit(s[0]) << 4 | hex_digit(s[1]));
    s += 2;
  }
  return n;
}

static unsigned __int128 parse_u128(const char *s) {
  unsigned __int128 v = 0;
  if (s[0] == '0' && s[1] == 'x') s += 2;
  for (; hex_digit(*s) >= 0; s++) v = v << 4 | (unsigned)hex_digit(*s);
  return v;
}

static uint8_t *byte_at(uint8_t memory[PAGE_COUNT][PAGE_BYTES], uint64_t address) {
  for (size_t i = 0; i < PAGE_COUNT; i++)
    if (address - pages[i].base < PAGE_BYTES) return &memory[i][address - pages[i].base];
  return NULL;
}

static void initial_memory(uint8_t memory[PAGE_COUNT][PAGE_BYTES]) {
  for (size_t i = 0; i < PAGE_COUNT; i++)
    for (uint64_t off = 0; off < PAGE_BYTES; off++)
      memory[i][off] = pages[i].base == CODE_PAGE ? CODE_FILL : fill_byte(pages[i].base + off);
}

// "asm | hex | key=value ..."; returns 0 on a comment or blank line.
static int parse_vector(char *line, struct vector *v, int lineno) {
  if (line[0] == '#' || line[0] == '\n' || line[0] == 0) return 0;
  char *bar1 = strchr(line, '|');
  char *bar2 = bar1 ? strchr(bar1 + 1, '|') : NULL;
  if (!bar2) {
    fprintf(stderr, "line %d: expected 'asm | hex | state'\n", lineno);
    exit(2);
  }
  memset(v, 0, sizeof *v);
  char *hex = bar1 + 1;
  while (*hex == ' ') hex++;
  v->code_len = parse_bytes(hex, v->code, 15);
  if (v->code_len <= 0) {
    fprintf(stderr, "line %d: bad instruction bytes\n", lineno);
    exit(2);
  }
  snprintf(v->hex, sizeof v->hex, "%.*s", v->code_len * 2, hex);
  v->at = DEFAULT_AT;
  for (int i = 0; i < 16; i++) {
    v->gpr[i] = default_gpr(i);
    v->xmm[i] = default_xmm(i);
  }
  strcpy(v->flags, "------");
  v->mxcsr = DEFAULT_MXCSR;
  initial_memory(v->memory);

  for (char *tok = strtok(bar2 + 1, " \t\n"); tok; tok = strtok(NULL, " \t\n")) {
    char *eq = strchr(tok, '=');
    if (!eq) goto bad;
    *eq = 0;
    char *val = eq + 1;
    int found = 0;
    for (int i = 0; i < 16; i++)
      if (!strcmp(tok, gpr_names[i])) v->gpr[i] = (uint64_t)parse_u128(val), found = 1;
    if (found) continue;
    if (!strncmp(tok, "xmm", 3)) {
      int i = atoi(tok + 3);
      if (i < 0 || i > 15) goto bad;
      v->xmm[i] = parse_u128(val);
    } else if (!strcmp(tok, "at")) {
      v->at = (uint64_t)parse_u128(val);
    } else if (!strcmp(tok, "flags")) {
      for (int i = 0; i < 6; i++)
        if (strchr(val, FLAG_LETTERS[i])) v->flags[i] = FLAG_LETTERS[i];
    } else if (!strcmp(tok, "known")) {
      // A deviation of the model, not of the start state.
    } else if (!strcmp(tok, "mxcsr")) {
      v->mxcsr = (uint32_t)parse_u128(val);
    } else if (!strcmp(tok, "mem")) {
      char *colon = strchr(val, ':');
      if (!colon) goto bad;
      uint64_t address = (uint64_t)parse_u128(val);
      uint8_t bytes[256];
      int n = parse_bytes(colon + 1, bytes, sizeof bytes);
      if (n < 0) goto bad;
      for (int i = 0; i < n; i++) {
        uint8_t *b = byte_at(v->memory, address + i);
        if (!b) goto bad;
        *b = bytes[i];
      }
    } else {
      goto bad;
    }
    continue;
  bad:
    fprintf(stderr, "line %d: bad field '%s'\n", lineno, tok);
    exit(2);
  }
  if (v->at + v->code_len > PAGE_BYTES) {
    // The instruction runs off the code page; only its first bytes are mapped.
    memcpy(&v->memory[0][v->at], v->code, PAGE_BYTES - v->at);
  } else {
    memcpy(&v->memory[0][v->at], v->code, v->code_len);
  }
  return 1;
}

// rosetta/oracle_signals.c reuses everything but the ptrace driver.
#ifndef ORACLE_SIGNALS
static void child(const struct vector *v) {
  if (ptrace(PTRACE_TRACEME, 0, 0, 0)) die("PTRACE_TRACEME");
  for (size_t i = 0; i < PAGE_COUNT; i++) {
    void *p = mmap((void *)pages[i].base, PAGE_BYTES, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (p != (void *)pages[i].base) die("mmap");
    memcpy(p, v->memory[i], PAGE_BYTES);
    if (mprotect(p, PAGE_BYTES, pages[i].prot)) die("mprotect");
  }
  raise(SIGSTOP);
  _exit(3);  // not reached: the parent kills us after one step
}

static void read_machine(pid_t pid, struct machine *m) {
  struct user_regs_struct r;
  struct user_fpregs_struct f;
  if (ptrace(PTRACE_GETREGS, pid, 0, &r)) die("PTRACE_GETREGS");
  if (ptrace(PTRACE_GETFPREGS, pid, 0, &f)) die("PTRACE_GETFPREGS");
  uint64_t g[16] = {r.rax, r.rcx, r.rdx, r.rbx, r.rsp, r.rbp, r.rsi, r.rdi,
                    r.r8,  r.r9,  r.r10, r.r11, r.r12, r.r13, r.r14, r.r15};
  memcpy(m->gpr, g, sizeof g);
  m->rip = r.rip;
  m->rflags = r.eflags;
  m->mxcsr = f.mxcsr;
  memcpy(m->xmm, f.xmm_space, sizeof m->xmm);
  char path[64];
  snprintf(path, sizeof path, "/proc/%d/mem", pid);
  int fd = open(path, O_RDONLY);
  if (fd < 0) die("open /proc/pid/mem");
  for (size_t i = 0; i < PAGE_COUNT; i++)
    if (pread(fd, m->memory[i], PAGE_BYTES, (off_t)pages[i].base) != PAGE_BYTES) die("pread");
  close(fd);
}

static void write_machine(pid_t pid, const struct vector *v) {
  struct user_regs_struct r;
  struct user_fpregs_struct f;
  if (ptrace(PTRACE_GETREGS, pid, 0, &r)) die("PTRACE_GETREGS");
  if (ptrace(PTRACE_GETFPREGS, pid, 0, &f)) die("PTRACE_GETFPREGS");
  const uint64_t *g = v->gpr;
  r.rax = g[0], r.rcx = g[1], r.rdx = g[2], r.rbx = g[3], r.rsp = g[4], r.rbp = g[5];
  r.rsi = g[6], r.rdi = g[7], r.r8 = g[8], r.r9 = g[9], r.r10 = g[10], r.r11 = g[11];
  r.r12 = g[12], r.r13 = g[13], r.r14 = g[14], r.r15 = g[15];
  r.rip = CODE_PAGE + v->at;
  for (int i = 0; i < 6; i++) {
    r.eflags &= ~(1ull << flag_bits[i]);
    if (v->flags[i] != '-') r.eflags |= 1ull << flag_bits[i];
  }
  r.eflags &= ~(1ull << 10);  // DF: string instructions are unsupported, but keep it defined
  f.mxcsr = v->mxcsr;
  memcpy(f.xmm_space, v->xmm, sizeof v->xmm);
  if (ptrace(PTRACE_SETREGS, pid, 0, &r)) die("PTRACE_SETREGS");
  if (ptrace(PTRACE_SETFPREGS, pid, 0, &f)) die("PTRACE_SETFPREGS");
}

#endif

static void print_hex128(unsigned __int128 x) {
  printf("0x%016llx%016llx", (unsigned long long)(x >> 64), (unsigned long long)x);
}

static void render_flags(char out[7], uint64_t rflags) {
  for (int i = 0; i < 6; i++) out[i] = rflags >> flag_bits[i] & 1 ? FLAG_LETTERS[i] : '-';
  out[6] = 0;
}

// Everything that differs from the input, in a fixed order. Faults keep `rip`
// unless it changed; a completed step always prints it.
static void print_diff(const struct machine *before, const struct machine *after, int completed) {
  if (completed || after->rip != before->rip) printf(" rip=0x%llx", (unsigned long long)after->rip);
  for (int i = 0; i < 16; i++)
    if (after->gpr[i] != before->gpr[i]) printf(" %s=0x%llx", gpr_names[i], (unsigned long long)after->gpr[i]);
  char fb[7], fa[7];
  render_flags(fb, before->rflags);
  render_flags(fa, after->rflags);
  if (strcmp(fa, fb)) printf(" flags=%s", fa);
  // Flags outside the model (DF, IF, ...); TF and RF belong to single-stepping.
  uint64_t other = ~(0x8d5ull | 1ull << 8 | 1ull << 16);
  if ((after->rflags ^ before->rflags) & other)
    printf(" rflags=0x%llx", (unsigned long long)after->rflags);
  for (int i = 0; i < 16; i++)
    if (after->xmm[i] != before->xmm[i]) {
      printf(" xmm%d=", i);
      print_hex128(after->xmm[i]);
    }
  if (after->mxcsr != before->mxcsr) printf(" mxcsr=0x%x", after->mxcsr);
  for (size_t p = 0; p < PAGE_COUNT; p++)
    for (int off = 0; off < PAGE_BYTES;) {
      if (after->memory[p][off] == before->memory[p][off]) {
        off++;
        continue;
      }
      printf(" mem=0x%llx:", (unsigned long long)(pages[p].base + off));
      while (off < PAGE_BYTES && after->memory[p][off] != before->memory[p][off])
        printf("%02x", after->memory[p][off++]);
    }
}

#ifndef ORACLE_SIGNALS
static void run(const struct vector *v) {
  pid_t pid = fork();
  if (pid < 0) die("fork");
  if (pid == 0) child(v);
  int status;
  if (waitpid(pid, &status, 0) < 0) die("waitpid");
  if (!WIFSTOPPED(status) || WSTOPSIG(status) != SIGSTOP) {
    fprintf(stderr, "%s: child did not stop (status %#x)\n", v->hex, status);
    exit(2);
  }
  write_machine(pid, v);
  struct machine before, after;
  read_machine(pid, &before);
  if (ptrace(PTRACE_SINGLESTEP, pid, 0, 0)) die("PTRACE_SINGLESTEP");
  if (waitpid(pid, &status, 0) < 0) die("waitpid");
  if (!WIFSTOPPED(status)) {
    fprintf(stderr, "%s: child exited (status %#x)\n", v->hex, status);
    exit(2);
  }
  read_machine(pid, &after);
  int sig = WSTOPSIG(status);
  siginfo_t si;
  if (ptrace(PTRACE_GETSIGINFO, pid, 0, &si)) die("PTRACE_GETSIGINFO");

  printf("%s |", v->hex);
  if (sig == SIGTRAP) {
    printf(" ok");
  } else if (sig == SIGSEGV && (si.si_code == SEGV_MAPERR || si.si_code == SEGV_ACCERR)) {
    printf(" pagefault %s 0x%llx", si.si_code == SEGV_MAPERR ? "unmapped" : "denied",
           (unsigned long long)(uintptr_t)si.si_addr);
  } else if (sig == SIGSEGV && si.si_code == SI_KERNEL) {
    printf(" gp");  // #GP, e.g. a misaligned 16-byte SSE operand
  } else if (sig == SIGILL) {
    printf(" ill");
  } else {
    printf(" signal %d code %d", sig, si.si_code);
  }
  print_diff(&before, &after, sig == SIGTRAP);
  printf("\n");
  kill(pid, SIGKILL);
  waitpid(pid, &status, 0);
}

int main(void) {
  static struct vector v;
  char line[8192];
  int lineno = 0;
  while (fgets(line, sizeof line, stdin)) {
    lineno++;
    if (parse_vector(line, &v, lineno)) {
      run(&v);
      fflush(stdout);
    }
  }
  return 0;
}
#endif
