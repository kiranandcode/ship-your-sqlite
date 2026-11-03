/* The rLimit column of date.c's aXformType[] is `float`: print the doubles
   the comparisons in parseModifier actually see. */
#include <stdio.h>
int main(void) {
  float a[] = {4.6427e+14, 7.7379e+12, 1.2897e+11, 5373485.0, 176546.0, 14713.0};
  for (int i = 0; i < 6; i++) printf("%.17g\n", (double)a[i]);
  return 0;
}
