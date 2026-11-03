/-
  An executable model of the libc / POSIX functions the SQLite export calls
  (BRIEF.md D5).

  Clean's `doStep` returns `none` at `Callstate (External (EF_external name sg) …)`,
  because CompCert leaves external functions uninterpreted. `Run.Runner`
  performs such calls with `callExternal` below and resumes at
  `Returnstate`. A call made this way is an instance of Clight's
  `step_external_function` rule under the external semantics this file
  defines; it is the part of the runner that `doStep_sound` does not cover,
  and it becomes the external-call parameter of the refinement statement
  (BRIEF.md D6).

  The model is pure: a `World` (output so far, errno cell, a fixed clock,
  the pthread mutexes as no-ops) threaded through the run. Memory is accessed
  only through `Mem.load`/`Mem.store`/`Mem.loadbytes`/`Mem.storebytes`, so
  `memcpy`/`memmove` copy pointer fragments faithfully.
-/
import CCLib

namespace Run
open CC

/-- Errors raised by the model. -/
inductive ExtErr where
  /-- outside the model: an external it does not implement, or a case of one it does not -/
  | unsupported (msg : String)
  /-- the call is undefined (bad pointer, undefined bytes, …) -/
  | ub (msg : String)
  deriving Repr

/-- The state of the outside world. -/
structure World where
  /-- the bytes of fd 0 not read yet -/
  stdin : ByteArray := .empty
  /-- bytes written to fd 1 -/
  out : ByteArray := .empty
  /-- bytes written to fd 2 -/
  err : ByteArray := .empty
  /-- the block holding `errno` (allocated on the first `__errno_location`) -/
  errnoBlock : Option Block := none
  /-- seconds since the epoch returned by `time`/`gettimeofday` -/
  clock : Nat := 0
  /-- `exit` was called with this status -/
  exited : Option Int := none
  /-- the static `struct tm` `localtime` returns (allocated on first use) -/
  tmBlock : Option Block := none
  /-- variadic activations: the block of one of the callee's locals ↦ the block
      holding its variadic arguments (8-byte slots), see `Run.Runner` -/
  va : List (Block × Block) := []

/-- The result of one external call. -/
structure ExtOut where
  world : World
  ret : Val
  mem : Mem

abbrev ExtM := Except ExtErr

def int32 (z : Int) : Val := .Vint (Integers.Int.repr z)
def int64 (z : Int) : Val := .Vlong (Integers.Int64.repr z)
/-- `size_t`/pointer-sized integers are `Vlong` on LP64 -/
def sizeV (n : Nat) : Val := .Vlong (Integers.Int64.repr n)

def argInt : Val → ExtM Int
  | .Vint n => pure (Integers.Int.signed n)
  | .Vlong n => pure (Integers.Int64.signed n)
  | v => throw (.ub s!"integer argument expected, got {repr v}")

def argNat (v : Val) : ExtM Nat := do
  match v with
  | .Vint n => pure (Integers.Int.unsigned n).toNat
  | .Vlong n => pure (Integers.Int64.unsigned n).toNat
  | v => throw (.ub s!"unsigned argument expected, got {repr v}")

def argFloat : Val → ExtM Floats.Float
  | .Vfloat f => pure f
  | v => throw (.ub s!"double argument expected, got {repr v}")

def argPtr : Val → ExtM (Block × Int)
  | .Vptr b o => pure (b, Integers.Ptrofs.unsigned o)
  | v => throw (.ub s!"pointer argument expected, got {repr v}")

/-- One concrete byte of memory. -/
def byteAt (m : Mem) (b : Block) (o : Int) : ExtM UInt8 :=
  match Mem.load .Mint8unsigned m b o with
  | some (.Vint c) => pure c.toNat.toUInt8
  | _ => throw (.ub s!"read of an undefined or inaccessible byte at offset {o}")

/-- `n` concrete bytes. -/
def bytesAt (m : Mem) (b : Block) (o : Int) (n : Nat) : ExtM ByteArray := do
  match Mem.loadbytes m b o n with
  | none => throw (.ub s!"read of {n} bytes at offset {o}: no permission")
  | some vs =>
    let mut acc := ByteArray.emptyWithCapacity n
    for v in vs do
      match v with
      | .Byte c => acc := acc.push c.toNat.toUInt8
      | _ => throw (.ub s!"read of {n} bytes at offset {o}: not all bytes are concrete")
    return acc

/-- Length of a NUL-terminated string. -/
def strLen (m : Mem) (b : Block) (o : Int) : ExtM Nat := do
  let mut i : Nat := 0
  repeat
    if (← byteAt m b (o + i)) == 0 then return i
    i := i + 1
  return i

def cString (m : Mem) (b : Block) (o : Int) : ExtM ByteArray := do
  bytesAt m b o (← strLen m b o)

def storeBytes (m : Mem) (b : Block) (o : Int) (bs : List UInt8) : ExtM Mem :=
  match Mem.storebytes m b o (bs.map fun c => .Byte (BitVec.ofNat 8 c.toNat)) with
  | some m' => pure m'
  | none => throw (.ub s!"write of {bs.length} bytes at offset {o}: no permission")

/-- Copy `n` memory values (pointer fragments included) — `memcpy`, `memmove`. -/
def copyVals (m : Mem) (bd : Block) (od : Int) (bs : Block) (os : Int) (n : Nat) : ExtM Mem := do
  if n == 0 then return m
  match Mem.loadbytes m bs os n with
  | none => throw (.ub "memcpy: source not readable")
  | some vs =>
    match Mem.storebytes m bd od vs with
    | some m' => pure m'
    | none => throw (.ub "memcpy: destination not writable")

/-- `malloc` as CompCert's `EF_malloc` does it: a block `[-8, n)` with the size at `-8`. -/
def mallocBlock (m : Mem) (n : Nat) : ExtM (Val × Mem) := do
  let (m', b) := Mem.alloc m (- sizeChunk Mptr) n
  match Mem.store Mptr m' b (- sizeChunk Mptr) (Val.Vptrofs (Integers.Ptrofs.repr n)) with
  | some m'' => pure (.Vptr b Integers.Ptrofs.zero, m'')
  | none => throw (.ub "malloc: header store failed")

def blockSize (m : Mem) (b : Block) : ExtM Nat := do
  match Mem.load Mptr m b (- sizeChunk Mptr) with
  | some (.Vlong n) => pure (Integers.Int64.unsigned n).toNat
  | _ => throw (.ub "realloc/free: not a malloc'ed block")

def freeBlock (m : Mem) (b : Block) : ExtM Mem := do
  let n ← blockSize m b
  match Mem.free m b (- sizeChunk Mptr) n with
  | some m' => pure m'
  | none => throw (.ub "free failed")

/-- The block holding `errno`. -/
def errnoCell (w : World) (m : Mem) : World × Block × Mem :=
  match w.errnoBlock with
  | some b => (w, b, m)
  | none =>
    let (m', b) := Mem.alloc m 0 4
    let m'' := (Mem.store .Mint32 m' b 0 (int32 0)).getD m'
    ({ w with errnoBlock := some b }, b, m'')

def setErrno (w : World) (m : Mem) (e : Int) : World × Mem :=
  let (w, b, m) := errnoCell w m
  (w, (Mem.store .Mint32 m b 0 (int32 e)).getD m)

def ENOENT : Int := 2
def ENOSYS : Int := 38

/-- A failing call: return `r` and set errno. -/
def failWith (w : World) (m : Mem) (e : Int) (r : Val) : ExtOut :=
  let (w, m) := setErrno w m e
  { world := w, ret := r, mem := m }

def unaryMath : String → Option (_root_.Float → _root_.Float)
  | "sin" => some Float.sin | "cos" => some Float.cos | "tan" => some Float.tan
  | "asin" => some Float.asin | "acos" => some Float.acos | "atan" => some Float.atan
  | "sinh" => some Float.sinh | "cosh" => some Float.cosh | "tanh" => some Float.tanh
  | "asinh" => some Float.asinh | "acosh" => some Float.acosh | "atanh" => some Float.atanh
  | "exp" => some Float.exp | "log" => some Float.log | "log10" => some Float.log10
  | "log2" => some Float.log2 | "sqrt" => some Float.sqrt | "ceil" => some Float.ceil
  | "floor" => some Float.floor | "fabs" => some Float.abs
  | "trunc" => some fun x => if x < 0 then Float.ceil x else Float.floor x
  | _ => none

/-- A finite double as `(negative, mantissa, exponent)`, value `± m · 2^e`. -/
def decodeFinite (x : _root_.Float) : Bool × Nat × Int :=
  let b := x.toBits.toNat
  let neg := b >>> 63 == 1
  let ex := (b >>> 52) % 2048
  let frac := b % 2 ^ 52
  if ex == 0 then (neg, frac, -1074) else (neg, frac + 2 ^ 52, (ex : Int) - 1075)

/-- C `fmod`: `x - n·y` with `n` = `x/y` truncated, computed exactly (the result
    is always representable). -/
def fmod (x y : _root_.Float) : _root_.Float :=
  if x.isNaN || y.isNaN || x.isInf || y == 0 then 0.0 / 0.0
  else if y.isInf || x == 0 then x
  else
    let (nx, mx, ex) := decodeFinite x
    let (_, my, ey) := decodeFinite y
    let e := min ex ey
    let X := mx * 2 ^ (ex - e).toNat
    let Y := my * 2 ^ (ey - e).toNat
    let r := Float.ofBinaryScientific (X % Y) e
    if nx then -r else r

def binaryMath : String → Option (_root_.Float → _root_.Float → _root_.Float)
  | "pow" => some Float.pow | "atan2" => some Float.atan2 | "fmod" => some fmod
  | _ => none

/-- The broken-down UTC time of `t` seconds since the epoch, as glibc's
    `struct tm` fields (sec, min, hour, mday, mon, year-1900, wday, yday, isdst);
    `none` when the year does not fit in an `int` (glibc returns NULL). -/
def utcBrokenDown (t : Int) : Option (List Int) :=
  let days := t / 86400
  let secs := t % 86400
  -- civil_from_days (H. Hinnant)
  let z := days + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := if m ≤ 2 then y + 1 else y
  let leap := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
  let cum : List Int := [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
  let yday := cum[(m - 1).toNat]! + d - 1 + (if leap && m > 2 then 1 else 0)
  let wday := ((days + 4) % 7 + 7) % 7
  if y - 1900 > 2147483647 || y - 1900 < -2147483648 then none
  else some [secs % 60, (secs / 60) % 60, secs / 3600, d, m - 1, y - 1900, wday, yday, 0]

/-- The external functions, by name. `none`: not modelled. -/
def callExternal (w : World) (name : String) (args : List Val) (m : Mem) :
    Option (ExtM ExtOut) :=
  let ok (r : Val) (m' : Mem := m) (w' : World := w) : ExtM ExtOut :=
    pure { world := w', ret := r, mem := m' }
  match name, args with
  -- output
  | "write", [fd, buf, n] => some do
      let fd ← argInt fd; let (b, o) ← argPtr buf; let n ← argNat n
      let bs ← bytesAt m b o n
      if fd == 1 then ok (int64 n) (w' := { w with out := w.out ++ bs })
      else if fd == 2 then ok (int64 n) (w' := { w with err := w.err ++ bs })
      else throw (.unsupported s!"write to fd {fd}")
  | "read", [fd, buf, n] => some do
      let fd ← argInt fd; let (b, o) ← argPtr buf; let n ← argNat n
      if fd != 0 then throw (.unsupported s!"read from fd {fd}") else
      let k := min n w.stdin.size
      let m' ← storeBytes m b o (w.stdin.extract 0 k).toList
      ok (int64 k) m' { w with stdin := w.stdin.extract k w.stdin.size }
  -- memory and strings
  | "realloc", [p, n] => some do
      let n ← argNat n
      match p with
      | .Vlong z => if z == 0 then do let (v, m') ← mallocBlock m n; ok v m'
                    else throw (.ub "realloc of a non-pointer")
      | .Vptr b o =>
        if Integers.Ptrofs.unsigned o != 0 then throw (.ub "realloc of an interior pointer") else
        let old ← blockSize m b
        let (v, m1) ← mallocBlock m n
        let (b', _) ← argPtr v
        let m2 ← copyVals m1 b' 0 b 0 (min old n)
        let m3 ← freeBlock m2 b
        ok v m3
      | _ => throw (.ub "realloc: bad pointer")
  | "memcpy", [d, s, n] | "memmove", [d, s, n] => some do
      let n ← argNat n
      if n == 0 then ok d else
      let (bd, od) ← argPtr d; let (bs, os) ← argPtr s
      ok d (← copyVals m bd od bs os n)
  | "memset", [d, c, n] => some do
      let n ← argNat n
      if n == 0 then ok d else
      let (bd, od) ← argPtr d; let c ← argInt c
      ok d (← storeBytes m bd od (List.replicate n (UInt8.ofNat (c % 256).toNat)))
  | "memcmp", [p, q, n] => some do
      let n ← argNat n
      if n == 0 then ok (int32 0) else
      let (bp, op) ← argPtr p; let (bq, oq) ← argPtr q
      let xs ← bytesAt m bp op n; let ys ← bytesAt m bq oq n
      let r := Id.run do
        for i in [0:n] do
          if xs[i]! != ys[i]! then return (xs[i]!.toNat : Int) - ys[i]!.toNat
        return 0
      ok (int32 r)
  | "memchr", [p, c, n] => some do
      let n ← argNat n; let c ← argInt c
      if n == 0 then ok (sizeV 0) else
      let (b, o) ← argPtr p
      let xs ← bytesAt m b o n
      match (List.range n).find? (fun i => xs[i]!.toNat == (c % 256).toNat) with
      | some i => ok (.Vptr b (Integers.Ptrofs.repr (o + i)))
      | none => ok (sizeV 0)
  | "strlen", [p] => some do
      let (b, o) ← argPtr p; ok (sizeV (← strLen m b o))
  | "strcmp", [p, q] | "strncmp", [p, q, _] => some do
      let lim ← match args with | [_, _, n] => argNat n | _ => pure (2 ^ 62)
      let (bp, op) ← argPtr p; let (bq, oq) ← argPtr q
      let mut i := 0
      let mut r : Int := 0
      while i < lim do
        let x ← byteAt m bp (op + i); let y ← byteAt m bq (oq + i)
        if x != y then r := (x.toNat : Int) - y.toNat; break
        if x == 0 then break
        i := i + 1
      ok (int32 r)
  | "strchr", [p, c] | "strrchr", [p, c] => some do
      let (b, o) ← argPtr p; let c := ((← argInt c) % 256).toNat
      let s ← cString m b o
      let hits := (List.range (s.size + 1)).filter fun i =>
        (if i == s.size then 0 else s[i]!.toNat) == c
      let pick := if name == "strchr" then hits.head? else hits.getLast?
      match pick with
      | some i => ok (.Vptr b (Integers.Ptrofs.repr (o + i)))
      | none => ok (sizeV 0)
  | "strspn", [p, q] | "strcspn", [p, q] => some do
      let (bp, op) ← argPtr p; let (bq, oq) ← argPtr q
      let s ← cString m bp op; let set ← cString m bq oq
      let inSet (c : UInt8) := set.toList.contains c
      let want := name == "strspn"
      let n := (s.toList.takeWhile fun c => inSet c == want).length
      ok (sizeV n)
  -- environment, process, time
  | "getenv", [_] => some (ok (sizeV 0))
  | "getpid", [] => some (ok (int32 1))
  | "geteuid", [] => some (ok (int32 1000))
  | "sysconf", [_] => some (ok (int64 4096))
  | "time", [p] => some do
      match p with
      | .Vptr b o =>
        match Mem.store .Mint64 m b (Integers.Ptrofs.unsigned o) (int64 w.clock) with
        | some m' => ok (int64 w.clock) m'
        | none => throw (.ub "time: bad pointer")
      | _ => ok (int64 w.clock)
  | "gettimeofday", [tv, _] => some do
      let (b, o) ← argPtr tv
      match Mem.store .Mint64 m b o (int64 w.clock) >>= (Mem.store .Mint64 · b (o + 8) (int64 0)) with
      | some m' => ok (int32 0) m'
      | none => throw (.ub "gettimeofday: bad pointer")
  | "__errno_location", [] => some do
      let (w', b, m') := errnoCell w m
      ok (.Vptr b Integers.Ptrofs.zero) m' w'
  -- single-threaded: mutexes always succeed
  | "pthread_mutex_init", _ | "pthread_mutex_destroy", _ | "pthread_mutex_lock", _
  | "pthread_mutex_unlock", _ | "pthread_mutex_trylock", _ | "pthread_mutexattr_init", _
  | "pthread_mutexattr_destroy", _ | "pthread_mutexattr_settype", _ => some (ok (int32 0))
  -- the file system is empty (Phase 1.5 replaces this by an in-memory one)
  | "open64", _ | "stat64", _ | "lstat64", _ | "access", _ => some (pure (failWith w m ENOENT (int32 (-1))))
  | "getcwd", [buf, n] => some do
      let (b, o) ← argPtr buf; let n ← argNat n
      if n < 2 then pure (failWith w m 34 (sizeV 0)) else
      ok buf (← storeBytes m b o ['/'.toUInt8, 0])
  -- localtime: the time zone is UTC (as in the semantics, Sql/DateTime.lean);
  -- glibc's x86-64 struct tm: nine ints, then tm_gmtoff and tm_zone (56 bytes)
  | "localtime", [tp] => some do
      let (b, o) ← argPtr tp
      let t ← match Mem.load .Mint64 m b o with
        | some (.Vlong n) => pure (Integers.Int64.signed n)
        | _ => throw (.ub "localtime: bad time_t")
      match utcBrokenDown t with
      | none => ok (sizeV 0)
      | some fields =>
        let (w1, tb, m1) := match w.tmBlock with
          | some tb => (w, tb, m)
          | none => let (m1, tb) := Mem.alloc m 0 56; ({ w with tmBlock := some tb }, tb, m1)
        let mut mm := m1
        for (v, i) in fields.zipIdx do
          match Mem.store .Mint32 mm tb (4 * i) (int32 v) with
          | some m' => mm := m'
          | none => throw (.ub "localtime: store")
        let some m2 := Mem.store .Mint64 mm tb 40 (int64 0) | throw (.ub "localtime: store")
        let some m3 := Mem.store .Mint64 m2 tb 48 (int64 0) | throw (.ub "localtime: store")
        ok (.Vptr tb Integers.Ptrofs.zero) m3 w1
  | "exit", [c] => some do
      ok .Vundef (w' := { w with exited := some (← argInt c) })
  -- libm: delegated to the host's libm through Lean's `Float` (the same glibc the native
  -- oracle links), as Clean does for arithmetic (LEAN.md §3)
  | f, [x] => (unaryMath f).map fun g => do
      ok (.Vfloat (Floats.Float.ofNative (g (← argFloat x).toNative)))
  | f, [x, y] => (binaryMath f).map fun g => do
      ok (.Vfloat (Floats.Float.ofNative (g (← argFloat x).toNative (← argFloat y).toNative)))
  | _, _ => none

end Run
