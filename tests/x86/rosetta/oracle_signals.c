// The oracle without ptrace, for Docker's linux/amd64 containers on Apple
// silicon, where Rosetta fails PTRACE_GETREGS and does not single-step.
// The vector's state is installed by returning from a signal handler with an
// edited ucontext; the instruction runs, and the int3 fill after it (or its
// fault) lands in a handler that records the machine. A completed step is
// SIGTRAP (rip = trap rip - 1), or a fetch fault at a new rip (the next
// instruction is not fetchable).
//
// A quick local check, not a replacement for CI's CPU: Rosetta does not keep
// AF, has no alignment check for SSE operands, reports some permission faults
// as unmapped, clears no ptest P/S/O, and rejects `nop eax`. See run.sh.

#define ORACLE_SIGNALS
#include "../oracle.c"

#include <ucontext.h>

static const struct vector *cur;
static struct machine before_m, after_m;
static int got_sig, got_code;
static uint64_t got_addr;

static void load_ctx(ucontext_t *uc, const struct vector *v, struct machine *b) {
  greg_t *g = uc->uc_mcontext.gregs;
  const int idx[16] = {REG_RAX, REG_RCX, REG_RDX, REG_RBX, REG_RSP, REG_RBP, REG_RSI, REG_RDI,
                       REG_R8, REG_R9, REG_R10, REG_R11, REG_R12, REG_R13, REG_R14, REG_R15};
  for (int i = 0; i < 16; i++) g[idx[i]] = (greg_t)v->gpr[i];
  g[REG_RIP] = (greg_t)(CODE_PAGE + v->at);
  uint64_t f = (uint64_t)g[REG_EFL];
  for (int i = 0; i < 6; i++) {
    f &= ~(1ull << flag_bits[i]);
    if (v->flags[i] != '-') f |= 1ull << flag_bits[i];
  }
  f &= ~(1ull << 10) & ~(1ull << 8);
  g[REG_EFL] = (greg_t)f;
  uc->uc_mcontext.fpregs->mxcsr = v->mxcsr;
  memcpy(uc->uc_mcontext.fpregs->_xmm, v->xmm, sizeof v->xmm);
  memcpy(b->gpr, v->gpr, sizeof b->gpr);
  b->rip = CODE_PAGE + v->at;
  b->rflags = f;
  b->mxcsr = v->mxcsr;
  memcpy(b->xmm, v->xmm, sizeof b->xmm);
  memcpy(b->memory, v->memory, sizeof b->memory);
}

static void save_ctx(ucontext_t *uc, struct machine *a) {
  greg_t *g = uc->uc_mcontext.gregs;
  const int idx[16] = {REG_RAX, REG_RCX, REG_RDX, REG_RBX, REG_RSP, REG_RBP, REG_RSI, REG_RDI,
                       REG_R8, REG_R9, REG_R10, REG_R11, REG_R12, REG_R13, REG_R14, REG_R15};
  for (int i = 0; i < 16; i++) a->gpr[i] = (uint64_t)g[idx[i]];
  a->rip = (uint64_t)g[REG_RIP];
  a->rflags = (uint64_t)g[REG_EFL];
  a->mxcsr = uc->uc_mcontext.fpregs->mxcsr;
  memcpy(a->xmm, uc->uc_mcontext.fpregs->_xmm, sizeof a->xmm);
  for (size_t i = 0; i < PAGE_COUNT; i++) memcpy(a->memory[i], (void *)pages[i].base, PAGE_BYTES);
}

static void on_start(int sig, siginfo_t *si, void *ctx) {
  (void)sig; (void)si;
  load_ctx(ctx, cur, &before_m);
}

static void on_stop(int sig, siginfo_t *si, void *ctx) {
  got_sig = sig; got_code = si->si_code; got_addr = (uint64_t)(uintptr_t)si->si_addr;
  save_ctx(ctx, &after_m);
  // Report from here: the interrupted state is not ours to resume.
  printf("%s |", cur->hex);
  int completed = 0;
  uint64_t start = before_m.rip;
  if (sig == SIGTRAP) {
    completed = 1;
    after_m.rip -= 1;  // past the int3
    printf(" ok");
  } else if (sig == SIGSEGV && (si->si_code == SEGV_MAPERR || si->si_code == SEGV_ACCERR) &&
             got_addr == after_m.rip && after_m.rip != start) {
    completed = 1;  // the instruction completed; fetching the next one faulted
    printf(" ok");
  } else if (sig == SIGSEGV && (si->si_code == SEGV_MAPERR || si->si_code == SEGV_ACCERR)) {
    printf(" pagefault %s 0x%llx", si->si_code == SEGV_MAPERR ? "unmapped" : "denied",
           (unsigned long long)got_addr);
  } else if (sig == SIGSEGV && si->si_code == SI_KERNEL) {
    printf(" gp");
  } else if (sig == SIGILL) {
    printf(" ill");
  } else {
    printf(" signal %d code %d", sig, si->si_code);
  }
  print_diff(&before_m, &after_m, completed);
  printf("\n");
  fflush(stdout);
  _exit(0);
}

static void child(const struct vector *v) {
  cur = v;
  static char alt[1 << 16];
  stack_t ss = {.ss_sp = alt, .ss_size = sizeof alt};
  if (sigaltstack(&ss, 0)) die("sigaltstack");
  struct sigaction sa = {0};
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
  sa.sa_sigaction = on_stop;
  int stops[] = {SIGTRAP, SIGSEGV, SIGBUS, SIGILL, SIGFPE};
  for (int i = 0; i < 5; i++) sigaction(stops[i], &sa, 0);
  sa.sa_sigaction = on_start;
  sigaction(SIGUSR1, &sa, 0);
  for (size_t i = 0; i < PAGE_COUNT; i++) {
    void *p = mmap((void *)pages[i].base, PAGE_BYTES, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (p != (void *)pages[i].base) die("mmap");
    memcpy(p, v->memory[i], PAGE_BYTES);
    if (mprotect(p, PAGE_BYTES, pages[i].prot)) die("mprotect");
  }
  raise(SIGUSR1);
  _exit(3);  // not reached
}

static void run(const struct vector *v) {
  fflush(stdout);
  pid_t pid = fork();
  if (pid < 0) die("fork");
  if (pid == 0) child(v);
  int status;
  if (waitpid(pid, &status, 0) < 0) die("waitpid");
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    printf("%s | oracle-crash status=%#x\n", v->hex, status);
    fflush(stdout);
  }
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
