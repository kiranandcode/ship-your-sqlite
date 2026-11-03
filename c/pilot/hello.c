/* Pilot program for the clightgen -lean pipeline (PHASES.md P.3). */
#include <stddef.h>
extern long write(int fd, const void *buf, unsigned long n);

struct point { int x; long y; };

static int sq(int v) { return v * v; }
static int twice(int (*f)(int), int v) { return f(f(v)); }

static void put(const char *s) {
  size_t n = 0;
  while (s[n]) n++;
  write(1, s, n);
}

static void putnum(long v) {
  char buf[24];
  int i = 23;
  int neg = v < 0;
  buf[i] = 0;
  if (v == 0) buf[--i] = '0';
  while (v != 0) { long d = v % 10; if (d < 0) d = -d; buf[--i] = (char)('0' + d); v /= 10; }
  if (neg) buf[--i] = '-';
  put(buf + i);
}

int main(void) {
  struct point p[4];
  long acc = 0;
  for (int i = 0; i < 4; i++) { p[i].x = i - 2; p[i].y = (long)i * 1000000007L; }
  for (int i = 0; i < 4; i++) acc += p[i].x * p[i].y;
  put("acc="); putnum(acc); put("\n");
  put("twice(sq,3)="); putnum(twice(sq, 3)); put("\n");
  return (int)(acc & 0x7f);
}
