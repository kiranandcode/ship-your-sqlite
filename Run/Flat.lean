/-
  Comparisons CompCert's memory model leaves undefined (PHASES.md O2).

  In CompCert's block memory model a pointer cast to an integer stays a
  `Vptr`, and `cmplu_bool` defines only `==`/`!=` between pointers into
  different blocks (and only for valid pointers), and nothing between a
  pointer and a nonzero integer. SQLite compares pointers into different
  allocations on purpose (`SQLITE_WITHIN`, the lookaside and page-cache
  checks `(uptr)p < (uptr)db->lookaside.pEnd`), so Clight is stuck there.

  The extension: blocks are placed in a flat address space at a fixed,
  injective place, `addr b o = b * 2^33 + 2^32 + o`, so a block whose offsets
  lie in (-2^32, 2^32) occupies its own interval and null (0) is below all of
  them. A comparison Clean's `semBinaryOperation` cannot decide is decided by
  comparing these addresses as unsigned 64-bit integers.

  It is applied as a rewrite of the expressions a statement evaluates in its
  next step: such a comparison is replaced by the constant it evaluates to,
  bottom-up, and `doStep` runs on the rewritten statement. Clight expressions
  are pure, so this is the same as evaluating the comparison in place.
-/
import CCLib

namespace Run
open CC

def flatAddr : Val → Option Int
  | .Vptr b o => some (((b.toNat : Int) * 2 ^ 33 + 2 ^ 32 + Integers.Ptrofs.unsigned o) % 2 ^ 64)
  | .Vlong n => some (Integers.Int64.unsigned n)
  | _ => none

def isCmp : Binop → Bool
  | .Oeq | .One | .Olt | .Ogt | .Ole | .Oge => true
  | _ => false

def flatCmp (op : Binop) (v1 v2 : Val) : Option Bool := do
  match v1, v2 with
  | .Vlong _, .Vlong _ => none     -- not a pointer comparison
  | _, _ =>
    let a ← flatAddr v1; let b ← flatAddr v2
    match op with
    | .Oeq => some (a == b) | .One => some (a != b)
    | .Olt => some (a < b) | .Ogt => some (a > b)
    | .Ole => some (a ≤ b) | .Oge => some (a ≥ b)
    | _ => none

/-- The byte a memory cell holds under the flat placement: a fragment of a
    stored pointer is the corresponding byte of its address (little-endian; the
    fragment at the lowest address has index 7). An uninitialised byte reads
    as 0: C gives it an unspecified value, and this is one choice of it. -/
def flatByte : MemVal → Option Nat
  | .Byte c => some c.toNat
  | .Fragment v _ i => (flatAddr v).map fun a => (a.toNat >>> (8 * (7 - i))) % 256
  | .Undef => some 0

def pointee : Ty → Option Ty
  | .Tpointer t _ | .Tarray t _ _ => some t
  | _ => none

def _root_.CC.Val.isPtr : Val → Bool
  | .Vptr .. => true
  | _ => false

/-- A pointer-valued operand as the integer constant of its flat address. -/
def concretize (a : Expr) (v : Val) : Expr :=
  match v with
  | .Vptr .. => match flatAddr v with
    | some n => .Econst_long (Integers.Int64.repr n) (typeof a)
    | none => a
  | _ => a

/-- Replace each comparison of `x` that Clean cannot evaluate, and the flat
    placement can, by its value. Returns the expression and whether it changed. -/
def flatRewrite (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) : Expr → Expr × Bool
  | .Ebinop op a1 a2 ty =>
    let (a1', c1) := flatRewrite ge e le m a1
    let (a2', c2) := flatRewrite ge e le m a2
    let x := Expr.Ebinop op a1' a2' ty
    if op == .Osub then
      -- pointer difference across blocks: on flat addresses, in elements
      match doEvalExpr ge e le m a1', doEvalExpr ge e le m a2', pointee (typeof a1') with
      | some v1@(.Vptr b1 _), some v2@(.Vptr b2 _), some t =>
        if b1 == b2 then (x, c1 || c2) else
        match flatAddr v1, flatAddr v2 with
        | some p1, some p2 =>
          let sz := max 1 (sizeof ge.genv_cenv t)
          (.Econst_long (Integers.Int64.repr ((p1 - p2) / sz)) ty, true)
        | _, _ => (x, c1 || c2)
      | _, _, _ => (x, c1 || c2)
    else
    -- any other binop Clean cannot evaluate because an operand is a pointer:
    -- that operand becomes its flat address, at the same C type
    match doEvalExpr ge e le m a1', doEvalExpr ge e le m a2' with
    | some v1, some v2 =>
      match Cop.semBinaryOperation ge.genv_cenv op v1 (typeof a1') v2 (typeof a2') m with
      | some _ => (x, c1 || c2)
      | none =>
        let a1'' := concretize a1' v1
        let a2'' := concretize a2' v2
        match doEvalExpr ge e le m a1'', doEvalExpr ge e le m a2'' with
        | some w1, some w2 =>
          match Cop.semBinaryOperation ge.genv_cenv op w1 (typeof a1'') w2 (typeof a2'') m with
          | some _ => (.Ebinop op a1'' a2'' ty, true)
          | none => (x, c1 || c2)
        | _, _ => (x, c1 || c2)
    | _, _ => (x, c1 || c2)
  | .Eunop op a ty =>
    let (a', c) := flatRewrite ge e le m a
    let x := Expr.Eunop op a' ty
    match doEvalExpr ge e le m a' with
    | some v =>
      match Cop.semUnaryOperation op v (typeof a') m with
      | some _ => (x, c)
      | none => (.Eunop op (concretize a' v) ty, v.isPtr || c)
    | none => (x, c)
  | .Ecast a ty =>
    let (a', c) := flatRewrite ge e le m a
    let x := Expr.Ecast a' ty
    match doEvalExpr ge e le m a' with
    | some v =>
      match Cop.semCast v (typeof a') ty m with
      | some _ => (x, c)
      | none => (.Ecast (concretize a' v) ty, v.isPtr || c)
    | none => (x, c)
  | .Ederef a ty =>
    let (a', c) := flatRewrite ge e le m a
    let x := Expr.Ederef a' ty
    -- a byte load that Clean evaluates to `Vundef`: the flat byte
    match ty, doEvalExpr ge e le m x, doEvalExpr ge e le m a' with
    | .Tint .I8 sg _, some .Vundef, some (.Vptr b o) =>
      match Mem.loadbytes m b (Integers.Ptrofs.unsigned o) 1 with
      | some [mv] =>
        match flatByte mv with
        | some n =>
          let z : Int := if sg == .Signed && n ≥ 128 then (n : Int) - 256 else n
          (.Econst_int (Integers.Int.repr z) ty, true)
        | none => (x, c)
      | _ => (x, c)
    | _, _, _ => (x, c)
  | .Efield a i ty => let (a', c) := flatRewrite ge e le m a; (.Efield a' i ty, c)
  | .Eaddrof a ty => let (a', c) := flatRewrite ge e le m a; (.Eaddrof a' ty, c)
  | x => (x, false)

/-- The statement with the expressions it evaluates in its next step rewritten. -/
def flatStmt (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) : Stmt → Option Stmt
  | s =>
    let rw := flatRewrite ge e le m
    let rws (al : List Expr) : List Expr × Bool :=
      al.foldr (fun a (acc, c) => let (a', c') := rw a; (a' :: acc, c || c')) ([], false)
    let r : Stmt × Bool := match s with
      | .Sifthenelse a s1 s2 => let (a', c) := rw a; (.Sifthenelse a' s1 s2, c)
      | .Sset i a => let (a', c) := rw a; (.Sset i a', c)
      | .Sassign a1 a2 =>
        let (a1', c1) := rw a1; let (a2', c2) := rw a2; (.Sassign a1' a2', c1 || c2)
      | .Scall o a al =>
        let (a', c1) := rw a; let (al', c2) := rws al; (.Scall o a' al', c1 || c2)
      | .Sbuiltin o ef tys al => let (al', c) := rws al; (.Sbuiltin o ef tys al', c)
      | .Sreturn (some a) => let (a', c) := rw a; (.Sreturn (some a'), c)
      | .Sswitch a sl => let (a', c) := rw a; (.Sswitch a' sl, c)
      | s => (s, false)
    if r.2 then some r.1 else none

end Run
