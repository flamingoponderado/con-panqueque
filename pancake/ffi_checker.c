/* The C side of the checker (pancake/checker.pnk).

   Pancake's memory (`@base`) is mapped at the fixed address PNK_BASE, so the layout the
   proofs fix (absolute heap, environment and memo addresses) is the run-time layout.

   FFI calls `@name(c, clen, a, alen)` become `ffiname(c, clen, a, alen)`:
     read  : the whole of stdin into a[0..alen): bytes 0..7 hold its length n (little-endian),
             the input follows from byte 8. An input that does not fit gets the length
             2^64-1, which the program's guard rejects (no verdict).
     accept: the program's accepting exit; prints "accept" and exits 0.
   Any other end (out of fuel, out of space, a rejected record) is not an acceptance. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define PNK_BASE ((void *)0x100000000UL)

extern void *cml_heap, *cml_stack, *cml_stackend;
extern char cake_codebuffer_begin, cake_codebuffer_end;
extern void cml_main(void);

void ffiread(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen < 16) exit(4);
  unsigned long cap = (unsigned long)alen - 8, n = 0;
  int ch;
  while ((ch = getchar()) != EOF) {
    if (n == cap) { n = ~0UL; break; }
    a[8 + n++] = (unsigned char)ch;
  }
  memcpy(a, &n, 8);
}

void ffiaccept(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen; (void)a; (void)alen;
  printf("accept\n");
  fflush(stdout);
  exit(0);
}

void cml_exit(int arg) { fflush(stdout); exit(arg ? arg : 1); }
void cml_err(int arg) { cml_exit(arg); }
void cml_clear(void) { __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end); }

static unsigned long env_mib(const char *name, unsigned long dflt) {
  const char *s = getenv(name);
  return s ? strtoul(s, NULL, 10) : dflt;
}

int main(void) {
  const unsigned long mib = 1024UL * 1024UL;
  unsigned long mem = env_mib("PNK_MEM_SIZE", 4096) * mib;
  unsigned long stack = env_mib("PNK_STACK_SIZE", 1024) * mib;
  char *m = mmap(PNK_BASE, mem + stack, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_FIXED_NOREPLACE, -1, 0);
  if (m == MAP_FAILED || m != PNK_BASE) { perror("mmap"); return 3; }
  cml_heap = m;
  cml_stack = m + mem;
  cml_stackend = m + mem + stack;
  cml_main();
  return 1; /* main returned without accepting */
}
