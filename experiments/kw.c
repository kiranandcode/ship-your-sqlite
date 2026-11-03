/* Print SQLite's keyword table: name and token code (for the Lean lexer). */
#include "sqlite3.c"
#include <stdio.h>
int main(void) {
  for (int i = 0; i <= SQLITE_N_KEYWORD; i++) { if (aKWLen[i] == 0) continue;
    char name[32]; int n = aKWLen[i];
    memcpy(name, zKWText + aKWOffset[i], n); name[n] = 0;
    printf("%s %d\n", name, aKWCode[i]);
  }
  return 0;
}
