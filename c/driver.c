/*
** The fixed driver linked with sqlite3.c (BRIEF.md, "The theorem we are after").
**
** Reads a whole SQL script from fd 0, opens an in-memory database, and runs the
** statements one by one with sqlite3_prepare_v2 / sqlite3_step. For every
** result row it prints one line: the columns separated by '|', each rendered
** as SQL's quote() does, so the storage class is visible:
**   NULL, an integer or a real (SQLite's own text rendering),
**   'text' (quotes doubled), X'hex' for blobs.
** A statement that fails prints "error: <errcode>: <message>" and the script
** goes on with the next statement. Nothing else is printed.
**
** Only write(2) and read(2) are used for I/O, so the same file runs natively
** and under the Clight interpreter with Run/Ext.lean's model.
*/
#include "sqlite3.h"

extern long read(int fd, void *buf, unsigned long n);
extern long write(int fd, const void *buf, unsigned long n);

static void out(const char *s, int n) {
  while (n > 0) {
    long k = write(1, s, (unsigned long)n);
    if (k <= 0) return;
    s += k; n -= (int)k;
  }
}

static int slen(const char *s) { int n = 0; while (s[n]) n++; return n; }
static void outs(const char *s) { out(s, slen(s)); }

static char *readAll(void) {
  int cap = 4096, n = 0;
  char *buf = sqlite3_malloc(cap + 1);
  if (buf == 0) return 0;
  for (;;) {
    long k;
    if (n == cap) {
      char *nb = sqlite3_realloc(buf, cap * 2 + 1);
      if (nb == 0) { sqlite3_free(buf); return 0; }
      buf = nb; cap *= 2;
    }
    k = read(0, buf + n, (unsigned long)(cap - n));
    if (k <= 0) break;
    n += (int)k;
  }
  buf[n] = 0;
  return buf;
}

static void printValue(sqlite3_stmt *st, int i) {
  switch (sqlite3_column_type(st, i)) {
    case SQLITE_NULL: outs("NULL"); break;
    case SQLITE_INTEGER:
    case SQLITE_FLOAT: {
      /* SQLite's own text rendering of the number (a REAL always shows a '.' or an exponent) */
      const char *z = (const char *)sqlite3_column_text(st, i);
      if (z) outs(z);
      break;
    }
    case SQLITE_TEXT: {
      const char *z = (const char *)sqlite3_column_text(st, i);
      int n = sqlite3_column_bytes(st, i), j, k = 0;
      out("'", 1);
      for (j = 0; j < n; j++) {
        if (z[j] == '\'') { out(z + k, j - k + 1); out("'", 1); k = j + 1; }
      }
      out(z + k, n - k);
      out("'", 1);
      break;
    }
    default: {
      const unsigned char *b = sqlite3_column_blob(st, i);
      int n = sqlite3_column_bytes(st, i), j;
      static const char hex[] = "0123456789ABCDEF";
      out("X'", 2);
      for (j = 0; j < n; j++) { char h[2]; h[0] = hex[b[j] >> 4]; h[1] = hex[b[j] & 15]; out(h, 2); }
      out("'", 1);
      break;
    }
  }
}

static void printError(sqlite3 *db) {
  char *z = sqlite3_mprintf("error: %d: %s\n", sqlite3_extended_errcode(db), sqlite3_errmsg(db));
  if (z) { outs(z); sqlite3_free(z); }
}

int main(void) {
  sqlite3 *db = 0;
  char *script;
  const char *tail;
  if (sqlite3_open(":memory:", &db) != SQLITE_OK) { outs("error: open\n"); return 1; }
  script = readAll();
  if (script == 0) { outs("error: out of memory\n"); return 1; }
  tail = script;
  while (*tail) {
    sqlite3_stmt *st = 0;
    const char *next = 0;
    int rc = sqlite3_prepare_v2(db, tail, -1, &st, &next);
    if (rc != SQLITE_OK) {
      printError(db);
      /* skip to the end of the failing statement, as the shell does */
      if (next == 0 || next == tail) {
        while (*tail && *tail != ';') tail++;
        if (*tail) tail++;
      } else {
        tail = next;
      }
      continue;
    }
    tail = next;
    if (st == 0) continue; /* whitespace or a comment */
    for (;;) {
      rc = sqlite3_step(st);
      if (rc == SQLITE_ROW) {
        int i, n = sqlite3_column_count(st);
        for (i = 0; i < n; i++) {
          if (i) out("|", 1);
          printValue(st, i);
        }
        out("\n", 1);
      } else {
        if (rc != SQLITE_DONE) printError(db);
        break;
      }
    }
    sqlite3_finalize(st);
  }
  sqlite3_free(script);
  sqlite3_close(db);
  return 0;
}
