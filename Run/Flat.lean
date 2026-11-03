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

/-- Replace each comparison of `x` that Clean cannot evaluate, and the flat
    placement can, by its value. Returns the expression and whether it changed. -/
partial def flatRewrite (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) : Expr → Expr × Bool
  | .Ebinop op a1 a2 ty =>
    let (a1', c1) := flatRewrite ge e le m a1
    let (a2', c2) := flatRewrite ge e le m a2
    let x := Expr.Ebinop op a1' a2' ty
    if !isCmp op then (x, c1 || c2) else
    match doEvalExpr ge e le m a1', doEvalExpr ge e le m a2' with
    | some v1, some v2 =>
      match Cop.semBinaryOperation ge.genv_cenv op v1 (typeof a1') v2 (typeof a2') m with
      | some _ => (x, c1 || c2)
      | none =>
        match flatCmp op v1 v2 with
        | some r => (.Econst_int (if r then Integers.Int.one else Integers.Int.zero) ty, true)
        | none => (x, c1 || c2)
    | _, _ => (x, c1 || c2)
  | .Eunop op a ty => let (a', c) := flatRewrite ge e le m a; (.Eunop op a' ty, c)
  | .Ecast a ty => let (a', c) := flatRewrite ge e le m a; (.Ecast a' ty, c)
  | .Ederef a ty => let (a', c) := flatRewrite ge e le m a; (.Ederef a' ty, c)
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
