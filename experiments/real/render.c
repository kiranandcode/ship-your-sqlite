/* Print N random finite doubles (bit patterns from a fixed xorshift seed, half
   of them "nice" decimals) with SQLite's REAL rendering, "%!.17g". */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "sqlite3.h"
static unsigned long long s = 88172645463325252ULL;
static unsigned long long rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
int main(int argc, char **argv) {
  long n = atol(argv[1]);
  if (argc > 2) { /* every binary exponent, n mantissas each */
    for (unsigned long long ex = 0; ex < 2047; ex++) for (long i = 0; i < n; i++) {
      unsigned long long b = (ex << 52) | (rnd() & 0xfffffffffffffULL); double d;
      if (i == 0) b = ex << 52;
      if (b == 0) continue;
      memcpy(&d, &b, 8);
      char *z = sqlite3_mprintf("%!.17g", d); printf("%016llx %s\n", b, z); sqlite3_free(z);
    }
    return 0;
  }
  for (long i = 0; i < n; i++) {
    double d; unsigned long long b = rnd();
    if (i % 2) { d = (double)(long long)(rnd() % 2000000001 - 1000000000) / (double)(1 + rnd() % 100000); }
    else { memcpy(&d, &b, 8); if (d != d || d - d != 0) continue; }
    memcpy(&b, &d, 8);
    char *z = sqlite3_mprintf("%!.17g", d);
    printf("%016llx %s\n", b, z); sqlite3_free(z);
  }
  return 0;
}
