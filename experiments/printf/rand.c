/* Randomized differential cases for SQLite's printf()/format(), round() and
   quote() of a REAL, answered by the native build (config/sqlite.flags).
     rand N [seed [R|Q|P|E]]  >  cases.txt      then   printf_check < cases.txt
   One case per line, every byte string in hex ("-" for empty):
     P <fmt> <arg>... = <result>      arg: i<int> r<bits> t<hex> b<hex> n
                                      result: T<hex> | N | E<code>
     R <bits> <n> <result bits>       round(r, n)
     Q <bits> <text>                  quote(r)
*/
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include "sqlite3.h"

static uint64_t s = 88172645463325252ULL;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
static int rn(int n) { return (int)(rnd() % (uint64_t)n); }

static void hex(const unsigned char *z, int n) {
  if (n == 0) { putchar('-'); return; }
  for (int i = 0; i < n; i++) printf("%02x", z[i]);
}

static double rdouble(void) {
  double d; uint64_t b;
  switch (rn(12)) {
    case 0: b = rnd(); memcpy(&d, &b, 8); if (d != d) d = 1.5; return d;
    case 1: return (double)(int64_t)(rnd() % 2000001 - 1000000) / 1000.0;
    case 2: return (double)(int64_t)(rnd() % 20001 - 10000) / 8.0;          /* exact halves */
    case 3: { double p = 1; int k = rn(40) - 20; while (k > 0) { p *= 10; k--; } while (k < 0) { p /= 10; k++; } return (rn(2) ? -1 : 1) * p * (1 + rn(9)); }
    case 4: return (double)(int64_t)(rnd() % 2000000001 - 1000000000) / (double)(1 + rnd() % 100000);
    case 5: { int e = rn(2046) + 1; b = ((uint64_t)e << 52) | (rnd() & 0xfffffffffffffULL); if (rn(2)) b |= 1ULL << 63; memcpy(&d, &b, 8); return d; }
    case 6: { static const double sp[] = {0.0, -0.0, 1e308, 1.7976931348623157e308, 5e-324, 2.2250738585072014e-308,
        0.5, 1.5, 2.5, -0.5, 0.05, 0.15, 0.25, 0.35, 1e15, 1e16, 1e17, 9.999999999999999e22, 1e23, 123456789012345678.0,
        0.1, 0.2, 0.3, 0.7, 0.9999999999999999, 4503599627370496.0, 4503599627370497.0, 9007199254740993.0, 1e-5, 1e-4, 99.995, 1.005, 2.675};
      return sp[rn(sizeof sp / sizeof sp[0])] * (rn(4) ? 1 : -1); }
    case 7: return (rn(2) ? 1 : -1) * (1.0 / 0.0);
    case 8: return (double)(int64_t)rnd();
    case 9: { double x = (double)(rnd() % 100000) / 100.0 + 0.005; return rn(2) ? x : -x; }
    case 10: { int e = rn(60) - 30; double p = 1; while (e > 0) { p *= 10; e--; } while (e < 0) { p /= 10; e++; } return p * (double)(rnd() % 1000000) / 1000.0; }
    default: { b = rnd(); memcpy(&d, &b, 8); if (d != d || d - d != 0) d = 0.1; return d; }
  }
}

static int64_t rint64(void) {
  switch (rn(8)) {
    case 0: return (int64_t)rnd();
    case 1: return rn(2001) - 1000;
    case 2: { static const int64_t sp[] = {0, 1, -1, 9, 10, 11, 12, 13, 21, 22, 23, 101, 111, 112, 1000, 999999,
        INT64_MAX, INT64_MIN, INT64_MIN + 1, 2147483647, 2147483648LL, -2147483648LL, -2147483649LL, 4294967295LL, 4294967296LL, 4294967297LL};
      return sp[rn(sizeof sp / sizeof sp[0])]; }
    case 3: return (int64_t)(rnd() % 100000000) - 50000000;
    case 4: return rn(60) - 30;
    default: return rn(100);
  }
}

static int rtext(unsigned char *z) {
  static const char *pieces[] = {"a", "b", "Z", " ", "'", "\"", "\\", "\n", "\t", "\x01", "\x1f", "\x7f", "%", "0", "1",
    "\xc3\xa9", "\xe2\x82\xac", "\xf0\x9f\x98\x80", "\x80", "\xc3", "12", "3.5", "-7", "1e5", "  42", "abc", "x", ".", ",",
    "\r", "\b", "\f", "\x0b", "inf", "9223372036854775808", "-0", "0x1F"};
  int n = 0, k = rn(8);
  for (int i = 0; i < k; i++) { const char *p = pieces[rn(sizeof pieces / sizeof pieces[0])]; int l = strlen(p); memcpy(z + n, p, l); n += l; }
  return n;
}

static char conv(void) {
  static const char cs[] = "dddiuxXoccsszqQwjJffeEggGGp%nr";
  int k = rn(100);
  if (k == 0) { static const char bad[] = "TSyk@lL0"; return bad[rn(sizeof bad - 1)]; }
  return cs[rn(sizeof cs - 1)];
}

/* use[k]: 1 if argument k (0-based, after the format) is read by a '*' */
static int use[64], nuse;
static int rfmt(char *f) {
  int n = 0; nuse = 0;
  int k = 1 + rn(3);
  for (int c = 0; c < k; c++) {
    if (rn(3) == 0) { static const char *lit[] = {"x", "ab ", "|", "%%", "\xc3\xa9", " "}; const char *p = lit[rn(6)]; strcpy(f + n, p); n += strlen(p); }
    f[n++] = '%';
    int nf = rn(4) == 0 ? rn(4) : rn(2);
    for (int i = 0; i < nf; i++) f[n++] = "-+ #!0,"[rn(7)];
    switch (rn(6)) {
      case 0: f[n++] = '*'; use[nuse++] = 1; break;
      case 1: case 2: n += sprintf(f + n, "%d", rn(4) == 0 ? rn(200) : rn(30)); break;
      default: break;
    }
    switch (rn(6)) {
      case 0: f[n++] = '.'; f[n++] = '*'; use[nuse++] = 2; break;
      case 1: case 2: n += sprintf(f + n, ".%d", rn(5) == 0 ? rn(400) : rn(25)); break;
      case 3: if (rn(3) == 0) f[n++] = '.'; break;
      default: break;
    }
    if (rn(10) == 0) { f[n++] = 'l'; if (rn(2)) f[n++] = 'l'; }
    char cv = conv(); f[n++] = cv;
    if (cv != '%' && cv != 'n') use[nuse++] = 0;
  }
  if (rn(8) == 0) f[n++] = '%';
  if (rn(4) == 0) { strcpy(f + n, " end"); n += 4; }
  f[n] = 0;
  return n;
}

int main(int argc, char **argv) {
  long N = atol(argv[1]);
  if (argc > 2) s ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL;
  sqlite3 *db; sqlite3_open(":memory:", &db);
  sqlite3_stmt *st[10];
  for (int a = 0; a < 10; a++) {
    char sql[200]; int n = sprintf(sql, "select %s(?1", rn(2) ? "printf" : "format");
    for (int j = 2; j <= a + 1; j++) n += sprintf(sql + n, ",?%d", j);
    sprintf(sql + n, ")");
    sqlite3_prepare_v2(db, sql, -1, &st[a], 0);
  }
  sqlite3_stmt *rd, *qt;
  sqlite3_prepare_v2(db, "select round(?1, ?2)", -1, &rd, 0);
  sqlite3_prepare_v2(db, "select quote(?1)", -1, &qt, 0);
  unsigned char buf[4096];
  if (argc > 3 && argv[3][0] == 'E') {
    /* every binary exponent, N mantissas each, 16 random float formats per value */
    sqlite3_stmt *p1; sqlite3_prepare_v2(db, "select printf(?1, ?2)", -1, &p1, 0);
    static const char *fl[] = {"", "!", "#", "!#", "+", "0", ",", "-"};
    for (uint64_t ex = 0; ex < 2048; ex++) for (long i = 0; i < N; i++) {
      uint64_t b = (ex << 52) | (i == 0 ? 0 : (rnd() & 0xfffffffffffffULL)); double d;
      if (rn(2)) b |= 1ULL << 63;
      memcpy(&d, &b, 8); if (d != d) continue;
      for (int k = 0; k < 16; k++) {
        char f[64]; int fl_ = sprintf(f, "%%%s%s.%d%c", fl[rn(8)], rn(4) ? "" : "12", rn(3) ? rn(22) : rn(60), "eEgGfgef"[rn(8)]);
        sqlite3_bind_text(p1, 1, f, fl_, SQLITE_TRANSIENT); sqlite3_bind_double(p1, 2, d);
        sqlite3_step(p1);
        printf("P t"); hex((unsigned char *)f, fl_); printf(" r%016llx = T", (unsigned long long)b);
        hex(sqlite3_column_text(p1, 0), sqlite3_column_bytes(p1, 0)); printf("\n");
        sqlite3_reset(p1);
      }
    }
    return 0;
  }
  for (long it = 0; it < N; it++) {
    int what = rn(10);
    if (argc > 3) what = argv[3][0] == 'R' ? 0 : argv[3][0] == 'Q' ? 1 : 2 + rn(8);   /* only round / quote / printf */
    if (what == 0) {
      double d = rdouble(); int n = rn(8) == 0 ? rn(31) : rn(6);
      if (rn(3) == 0) d = (double)(int64_t)(rnd() % 2000001 - 1000000) / (double)(1 + rn(10000));
      sqlite3_bind_double(rd, 1, d); sqlite3_bind_int(rd, 2, n);
      sqlite3_step(rd); double r = sqlite3_column_double(rd, 0); sqlite3_reset(rd);
      uint64_t b, rb; memcpy(&b, &d, 8); memcpy(&rb, &r, 8);
      printf("R %016llx %d %016llx\n", (unsigned long long)b, n, (unsigned long long)rb);
      continue;
    }
    if (what == 1) {
      double d = rdouble(); uint64_t b; memcpy(&b, &d, 8);
      sqlite3_bind_double(qt, 1, d); sqlite3_step(qt);
      printf("Q %016llx ", (unsigned long long)b); hex(sqlite3_column_text(qt, 0), sqlite3_column_bytes(qt, 0)); printf("\n");
      sqlite3_reset(qt);
      continue;
    }
    char f[1024]; int fl = rfmt(f);
    int na = rn(10);
    sqlite3_stmt *p = st[na];
    printf("P ");
    if (rn(50) == 0) { sqlite3_bind_null(p, 1); printf("n"); }
    else { sqlite3_bind_text(p, 1, f, fl, SQLITE_TRANSIENT); printf("t"); hex((unsigned char *)f, fl); }
    for (int j = 2; j <= na + 1; j++) {
      int t = rn(10);
      if (j - 2 < nuse && use[j - 2]) {
        /* a width (1) or precision (2): small, or one that makes SQLite give
           up or wraps to a small int (never a legal huge result) */
        static const int64_t bigw[] = {1000000000, 2147483647, -2147483647, -2147483648LL, 2147483648LL, 4294967297LL, 3000000000LL, -1000000000};
        static const int64_t bigp[] = {-2147483648LL, 2147483648LL, 4294967297LL, -4294967295LL};
        int k = rn(20);
        if (k == 0) { int64_t v = use[j - 2] == 1 ? bigw[rn(8)] : bigp[rn(4)]; sqlite3_bind_int64(p, j, v); printf(" i%lld", (long long)v); }
        else if (k == 1) { double d = (rn(41) - 20) + 0.75; uint64_t b; memcpy(&b, &d, 8); sqlite3_bind_double(p, j, d); printf(" r%016llx", (unsigned long long)b); }
        else if (k == 2) { char t[8]; int l = sprintf(t, " %d", rn(30) - 5); sqlite3_bind_text(p, j, t, l, SQLITE_TRANSIENT); printf(" t"); hex((unsigned char *)t, l); }
        else if (k == 3) { sqlite3_bind_null(p, j); printf(" n"); }
        else { int64_t v = rn(81) - 40; sqlite3_bind_int64(p, j, v); printf(" i%lld", (long long)v); }
        continue;
      }
      if (t < 3) { int64_t v = rint64(); sqlite3_bind_int64(p, j, v); printf(" i%lld", (long long)v); }
      else if (t < 6) { double d = rdouble(); uint64_t b; memcpy(&b, &d, 8); sqlite3_bind_double(p, j, d); printf(" r%016llx", (unsigned long long)b); }
      else if (t < 8) { int l = rtext(buf); sqlite3_bind_text(p, j, (char *)buf, l, SQLITE_TRANSIENT); printf(" t"); hex(buf, l); }
      else if (t < 9) { sqlite3_bind_null(p, j); printf(" n"); }
      else { int l = rtext(buf); if (rn(3) == 0) buf[l++] = 0; sqlite3_bind_blob(p, j, buf, l, SQLITE_TRANSIENT); printf(" b"); hex(buf, l); }
    }
    int rc = sqlite3_step(p);
    printf(" = ");
    if (rc == SQLITE_ROW) {
      if (sqlite3_column_type(p, 0) == SQLITE_NULL) printf("N");
      else { const unsigned char *z = sqlite3_column_text(p, 0); printf("T"); hex(z, sqlite3_column_bytes(p, 0)); }
    } else printf("E%d", sqlite3_extended_errcode(db));
    printf("\n");
    sqlite3_reset(p);
    sqlite3_clear_bindings(p);
  }
  return 0;
}
