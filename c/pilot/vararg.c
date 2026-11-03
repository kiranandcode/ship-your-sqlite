/* Pilot: a user-defined variadic function (SQLite's printf family is one). */
#include <stdarg.h>
extern long write(int fd, const void *buf, unsigned long n);
static long sum(int n, ...) {
  va_list ap; long s = 0;
  va_start(ap, n);
  for (int i = 0; i < n; i++) s += va_arg(ap, long);
  va_end(ap);
  return s;
}
int main(void) { return (int)sum(3, 10L, 20L, 12L); }
