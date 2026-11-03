# TRUST: the semantics the theorem is about

`SqliteRefines_Statement` (BRIEF.md) relates SQLite's C code to the SQL
semantics through a step relation on Clight states. That relation is **Certora/
clean's Clight step relation (`CC.Step`, a Lean port of CompCert 3.17's Clight)
plus exactly three extensions**, all defined in this repository. Kiran approved
this design on 2026-11-03 (BRIEF.md D8).

This file says, for each extension, what it adds to CompCert's semantics, why,
and which SQLite code needs it. Anything here that SQLite does not exercise is
not an extension. Today the extensions live in the runner (`Run/`), which
executes them. Phase 3.1 states the same rules as an inductive relation
`StepX` and proves that the runner follows it, as Clean does with
`doStep_sound`.

What is trusted without any extension, unchanged from Clean (its `export/LEAN.md`
§9): the `clightgen` front end (C → Clight, shared with CompCert), the fidelity of
the Lean port to Rocq's Clight (differentially tested by Clean, and by
ship-your-tcc on 345 programs), IEEE arithmetic delegated to the host, and Lean.

## Not an extension: volatile accesses

`clightgen -normalize` turns a volatile access into the builtins `EF_vload` /
`EF_vstore`. Clean's *relation* defines them (`Events.VolatileLoad`,
`VolatileStore`). For a block that is not a volatile global, the rule
`nonvol` makes them an ordinary `Mem.load` / `Mem.store` with an empty trace,
as in CompCert. Clean's *interpreter* does not execute them. Our runner
implements exactly the `nonvol` rule and refuses volatile globals (SQLite has
none on Linux). SQLite needs this for `db->u1.isInterrupted` (`volatile int`)
and the WAL index (`volatile u32 *`).

## Extension 1: the external-call model (`Run/Ext.lean`)

**CompCert / Clean.** An external function is uninterpreted. Clean declares
`axiom externalFunctionsSem : String → Signature → ExtcallSem`, and its
interpreter stops at every `EF_external` call. Only `malloc`, `free`, `memcpy`
(the builtin used for struct copies) and annotations have a meaning.

**What we add.** A pure model of the libc/POSIX functions the export calls (85
names in the D7 build). The state of the outside world is a `World`: stdin
(the script), stdout and stderr, the `errno` cell, a clock, and an exit
status. The model is defined by cases in `callExternal`:

| group | functions | meaning |
|---|---|---|
| I/O | `read` (fd 0), `write` (fd 1, 2) | stdin is the script; output is appended to the World |
| memory | `realloc`; `memcpy`, `memmove`, `memset`, `memcmp`, `memchr` | `realloc` uses the block layout of CompCert's `EF_malloc` (size at offset −8). Copies go through `Mem.loadbytes`/`storebytes`, so pointer fragments survive a copy as they do in CompCert's memory |
| strings | `strlen`, `strcmp`, `strncmp`, `strchr`, `strrchr`, `strspn`, `strcspn` | ISO C, reading concrete bytes; a non-concrete byte is undefined behaviour (the run stops) |
| libm | `sin` … `atanh`, `exp`, `log`, `log10`, `log2`, `pow`, `atan2`, `sqrt`, `ceil`, `floor`, `trunc`, `fabs` | delegated to the host's libm through Lean's `Float`, as Clean delegates arithmetic. `fmod` is exact (`Run.fmod`) |
| process | `getpid` = 1, `geteuid` = 1000, `getenv` = NULL, `sysconf` = 4096, `getcwd` = "/", `exit` | fixed values |
| time | `time`, `gettimeofday` | a fixed clock (`World.clock`, 0 by default). So `'now'` and `random()` are deterministic: SQLite seeds its PRNG from `/dev/urandom`, which does not exist here, and falls back to time and pid |
| threads | `pthread_mutex_*`, `pthread_mutexattr_*` | succeed and do nothing: the program is single-threaded (`SQLITE_THREADSAFE=1` is the default build; its mutexes are never contended) |
| files | `open64`, `stat64`, `lstat64`, `access` | fail with `ENOENT`: the file system is empty. Phase 1.5 replaces this by an in-memory file system so that file databases, `ATTACH` of files and temp files run |

Unmodelled names (`dlopen`, `mmap64`, `pread64`, …) stop the run as
"unsupported", which `scripts/difftest.sh` reports. The run never continues with
an unknown result.

**Why.** No SQLite run gets past `sqlite3_initialize` without `memset`,
`memcpy`, `pthread_mutex_*` and `getenv`.

**For the theorem.** The model is a parameter of `StepX`, not an axiom (CLAUDE.md
law 2). `SqliteRefines_Statement` is stated for this model. A variant for any
model satisfying a specification (the POSIX contract of each function) is the
stronger statement Phase 3 aims at.

## Extension 2: variadic calls (`Run/Runner.lean`, "Variadic calls"; PHASES.md O1)

**CompCert / Clean.** Clight has no rule for a call that passes variadic
arguments. `step_call` evaluates the arguments with `eval_exprlist … tyargs`,
one parameter type per argument, so a call with more arguments than
parameters is stuck. `__builtin_va_start`, `__compcert_va_int32/int64/float64`,
`__builtin_va_copy` and `__builtin_va_end` are uninterpreted builtins.
(CompCert's back ends give these calls their meaning below Clight, so its
correctness theorem says nothing about programs that use them.)

**What we add.**
- *Call.* At `Scall` of a function whose type has `cc_vararg = some n`, with
  more arguments than parameters: the fixed arguments are evaluated and cast to
  the parameter types, and the variadic ones evaluated at their own types. The
  front end has already applied the default argument promotions, and an array
  argument evaluates to its address. The variadic values are stored in a
  fresh block, one 8-byte slot each (`Mint32` for an `int`, `Mint64` for a
  `long` or pointer, `Mfloat64` for a `double`), and the call proceeds with the
  fixed arguments. The block is associated with the callee's activation,
  identified by the smallest block among its locals.
- *`va_start(ap)`.* Stores a pointer to the first slot in the first word of
  `ap`. CompCert declares `va_list` as `tarray tulong 3`.
- *`va_arg`.* `__compcert_va_int32/int64/float64(ap)` load one slot at the
  matching chunk and advance the cursor by 8.
- *`va_copy`* copies the cursor; *`va_end`* does nothing.
- A variadic **external** function (`fcntl64`) receives all its arguments in
  the external model.

**Why.** SQLite has 20 variadic functions (`sqlite3MPrintf`,
`sqlite3_mprintf`, `sqlite3_snprintf`, `sqlite3ErrorMsg`,
`sqlite3ErrorWithMsg`, `sqlite3NestedParse`, `sqlite3VdbeExplain`,
`sqlite3VdbeMultiLoad`, `sqlite3_str_appendf`, `sqlite3_config`,
`sqlite3_db_config`, `jsonPrintf`, …) with about 600 call sites, and passes
`va_list` down to `sqlite3_str_vappendf`. Every error message, every nested SQL
statement (schema initialisation, `sqlite_sequence`, ALTER TABLE) and every
`printf()`/`format()` goes through them. Reproducer: `c/pilot/vararg.c` is
stuck after 3 steps in Clean, and `c/pilot/vararg2.c` matches gcc under the
extension.

## Extension 3: flat placement of blocks (`Run/Flat.lean`; PHASES.md O2)

**CompCert / Clean.** Memory is a set of disjoint blocks with no addresses. A
pointer cast to an integer type stays a pointer value (`Vptr b ofs`). Defined
operations on pointers: arithmetic within a block, subtraction and ordering of
two pointers into the *same* block, and `==`/`!=` against another valid
pointer or null. Everything else is undefined (`None`, so the program is
stuck). That includes `<` between pointers into different blocks, any integer
arithmetic on a pointer cast to an integer, subtracting pointers into
different blocks, and reading one byte of a stored pointer (that yields
`Vundef`).

**What we add.** Block `b` is placed at the fixed address
`b·2³³ + 2³²` (mod 2⁶⁴). Every block's offsets fit in (−2³², 2³²), so blocks
occupy disjoint intervals and null (0) is below all of them. When Clean's
evaluation of an expression fails *only* because a pointer is used as an
integer, the pointer is taken to be its flat address:

| case | rule |
|---|---|
| comparison | a comparison Clean cannot decide compares the flat addresses as unsigned 64-bit integers |
| pointer subtraction across blocks | `(addr p − addr q) / sizeof(*p)` |
| integer arithmetic, casts, unary ops | a pointer operand is replaced by the integer constant of its flat address, at the same C type |
| byte load of a stored pointer | a fragment of pointer `v` (the one at the lowest address has index 7) reads as byte `7−i` of `addr v`, little-endian |
| byte load of an uninitialised byte | reads as 0. C gives such a byte an unspecified value (for `unsigned char`), and 0 is one choice. It applies only where Clean's load produced `Vundef` and a byte was expected |

The rule is applied by rewriting the expressions of the current step (and of an
`Sset` that stored a `Vundef` byte) into constants, then letting Clean's
`doStep` take the step. Clight expressions are pure, so this equals evaluating
in place. It is never used where Clean's evaluation succeeds. So every run
of the extended relation that never needs the rule is a run of Clean's
relation.

**Why, case by case.**
- *Comparisons.* SQLite's allocator decides whether a pointer belongs to the
  lookaside buffer by comparing it with the buffer's bounds:
  `(uptr)p < (uptr)db->lookaside.pEnd` in `sqlite3DbRealloc`, `sqlite3DbFreeNN`,
  `sqlite3DbMallocSize`, and `SQLITE_WITHIN` in `isLookaside` and the page cache.
  `select 1;` is stuck at the first such comparison (80,640 steps).
- *Subtraction across blocks.* `sqlite3EndTable` computes
  `13 + (pCons->z − pParse->sNameToken.z)` with the second pointer into a
  freed buffer, for AUTOINCREMENT tables. This is undefined in ISO C too, and the
  result is garbage natively and here alike; it is discarded by a schema reload
  (BUGS.md #1).
- *Integer arithmetic on pointers.* `%p` in `sqlite3_str_vappendf`, used by
  `RETURNING` to name its internal table `sqlite_returning_%p`.
- *Byte loads of pointers.* `vdbeRecordCompareInt` reads 8 bytes for every
  integer serial type and shifts the unused ones out. The extra bytes are
  padding that may hold a stale pointer (BUGS.md #2).

**How much.** In the six differential scripts the rule decides 1,709–8,511 of
0.86M–5.6M steps (`--stats` reports `flat=`). `--trace-flat` prints each use.

**Soundness against a real machine.** Under any placement of disjoint blocks,
these operations give the same answer for every use SQLite makes of them
(membership in a buffer, or a value that is shifted out or discarded), so the
choice of placement does not affect SQLite's output. The differential tests
check this (the native addresses are different). Phase 3 turns it into a
lemma: the output of a run does not depend on the placement.

## How to check that a run uses only these extensions

`sqlite_run --stats` prints `externals=` (extension 1) and `flat=`
(extension 3); variadic calls are counted in `steps`. A run that ends `STUCK`
or `UNSUPPORTED` has reached something outside Clean's relation *and* these
extensions, and is never counted as passing.
