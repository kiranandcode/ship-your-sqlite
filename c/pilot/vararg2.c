/* Pilot: va_list passed down (SQLite's sqlite3_str_vappendf shape), pointers,
   doubles, ints, a variadic call with no variadic argument. */
#include <stdarg.h>
extern long write(int fd, const void *buf, unsigned long n);
static void putc1(char c) { write(1, &c, 1); }
static void putnum(long v) { char b[24]; int i = 23; b[i] = 0; if (v < 0) { putc1('-'); v = -v; }
  if (v == 0) b[--i] = '0'; while (v) { b[--i] = '0' + v % 10; v /= 10; } write(1, b + i, 23 - i); }
static void vfmt(const char *f, va_list ap) {
  for (; *f; f++) {
    if (*f != '%') { putc1(*f); continue; }
    f++;
    if (*f == 'd') putnum(va_arg(ap, int));
    else if (*f == 'l') putnum(va_arg(ap, long));
    else if (*f == 's') { const char *s = va_arg(ap, const char *); while (*s) putc1(*s++); }
    else if (*f == 'f') putnum((long)(va_arg(ap, double) * 1000));
  }
}
static void fmt(const char *f, ...) { va_list ap; va_start(ap, f); vfmt(f, ap); va_end(ap); }
int main(void) {
  fmt("int=%d long=%l str=%s dbl=%f\n", -7, 1234567890123L, "hi", 3.14159);
  fmt("none\n");
  return 0;
}
