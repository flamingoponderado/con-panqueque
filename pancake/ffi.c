/* The C side of con-panqueque's Pancake programs.

   Pancake's memory (`@base`) is the region CakeML calls the heap; a Pancake
   program manages it itself (no collector). FFI calls `@name(c, clen, a, alen)`
   become `ffiname(c, clen, a, alen)`:
     read : a[0] = 0 at end of input, else a[0] = 1 and a[1] = the next byte;
     write: a[0..7] is a 64-bit word, printed in decimal (milestone 0 only). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern char cake_codebuffer_begin, cake_codebuffer_end;
extern void cml_main(void);

void ffiread(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen < 2) exit(4);
  int ch = getchar();
  if (ch == EOF) a[0] = 0;
  else { a[0] = 1; a[1] = (unsigned char)ch; }
}

void ffiwrite(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen < 8) exit(4);
  unsigned long v;
  memcpy(&v, a, 8);
  printf("%lu\n", v);
}

void cml_exit(int arg) { fflush(stdout); exit(arg); }
void cml_err(int arg) { cml_exit(arg); }
void cml_clear(void) { __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end); }

static unsigned long env_mib(const char *name, unsigned long dflt) {
  const char *s = getenv(name);
  return s ? strtoul(s, NULL, 10) : dflt;
}

int main(void) {
  const unsigned long mib = 1024UL * 1024UL;
  unsigned long mem = env_mib("PNK_MEM_SIZE", 1024) * mib;
  unsigned long stack = env_mib("PNK_STACK_SIZE", 1024) * mib;
  char *m = mmap(NULL, mem + stack, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (m == MAP_FAILED) { perror("mmap"); return 3; }
  cml_heap = m;
  cml_stack = m + mem;
  cml_stackend = m + mem + stack;
  cml_main();
  return 0;
}
