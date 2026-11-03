# Behaviour of SQLite found by the Clight semantics

Places where SQLite 3.54.1 does something C or CompCert's memory model leaves
undefined. Each was found because Clean's interpreter got stuck, and was
checked natively with gdb.

| # | where | what | effect natively |
|---|---|---|---|
| 1 | `sqlite3EndTable`, sqlite3.c:129842 | For a `CREATE TABLE … AUTOINCREMENT` that creates `sqlite_sequence`, the nested parse runs before `p->u.tab.addColOffset = 13 + (int)(pCons->z - pParse->sNameToken.z)`, and afterwards `sNameToken.z` points into the nested statement's SQL text, which has already been freed. The subtraction is between pointers into different allocations (undefined in ISO C; stuck in CompCert). Reproducer: `create table t(k integer primary key autoincrement, name text);` | gdb on the gcc build: `diff=-15415`, so `addColOffset` is garbage. Harmless, because the schema change reloads the schema and rebuilds the `Table` with the correct offset (48) before ALTER TABLE can read it |
| 2 | `vdbeRecordCompareInt` (92440) | Reads 8 bytes for every integer serial type and shifts the extra ones away. The extra bytes are padding after the record (SQLite guarantees 74 bytes), which may hold anything, here a stale pointer of the page cache. Defined in C (the bytes are allocated), but CompCert cannot read the bytes of a stored pointer | none: the bytes are shifted out. Documented in the source |
| 3 | `computeJD` (date.c), via `parseHhMmSs` | A fractional-seconds field of 309 or more digits makes the parser compute `ms/rScale` as inf/inf = NaN, and `computeJD` then evaluates `(sqlite3_int64)(p->s*1000 + 0.5)`: a NaN converted to an integer, undefined in ISO C (C11 6.3.1.4) and stuck in CompCert's semantics. Reproducer: `SELECT time('12:00:00.' \|\| replace(hex(zeroblob(200)), '0', '9'), 'subsec');` | x86's `cvttsd2si` gives 0x8000000000000000; SQLite then reports the time value invalid and returns NULL. The semantics (Sql/DateTime.lean) reproduces the x86 result; the Clight export is stuck (tests/sem/datetime_edge.sql, datetime_basic.sql) |
