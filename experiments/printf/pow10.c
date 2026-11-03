/* Print powerOfTen(p) for every p in [-348, 347] (the statics of sqlite3.c are
   reachable because the amalgamation is #included). Compare with the exact
   floor(10^p * 2^(63 - pwr10to2(p))) by pow10.py. */
#include "sqlite3.c"
int main(void){
  for (int p = POWERSOF10_FIRST; p <= POWERSOF10_LAST; p++) {
    u32 lo; u64 h = powerOfTen(p, &lo);
    printf("%d %llu %u\n", p, (unsigned long long)h, lo);
  }
  return 0;
}
