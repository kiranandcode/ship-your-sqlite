/-
  Whole-program runner: Clean's `CC.doStep` (proved sound, `doStep_sound`)
  plus the external-call model of `Run.Ext` at the states where `doStep` stops
  on an `EF_external` call.

  Adapted from ship-your-tcc's `lean/ClightRun/ClightRun/Run.lean`
  (ATTRIBUTION.md): the pure tail-recursive loop and the stuck-state
  diagnosis are theirs; the external model and the `World` threading are ours.
-/
import CCLib
import Run.Ext
import Run.Flat

namespace Run
open CC

/-- Why the pure loop stopped. -/
inductive Stop where
  | done (r : Integers.Int)
  | stuck (s : State)
  | fuel (s : State)
  /-- an `Sset` of a byte load stored `Vundef` (state before the step, and Clean's step) -/
  | undefByte (s s' : State)

instance : Inhabited Stop := ⟨.done 0⟩

/-- Run `doStep` until a final state, a stuck state, or `limit` steps
    (`limit = 0`: unbounded). Tail-recursive, so it compiles to a loop. -/
partial def runPure (ge : CGenv) (s : State) (n limit : Nat) : Stop × Nat :=
  match s with
  | .Returnstate (.Vint r) .Kstop _ => (.done r, n)
  | _ =>
    if limit != 0 && n ≥ limit then (.fuel s, n) else
    match doStep ge s with
    | some (_, s') =>
      match s, s' with
      | .State _ (.Sset id (.Ederef _ (.Tint .I8 _ _))) _ _ _ _, .State _ _ _ _ le' _ =>
        if le'.get id == some .Vundef then (.undefByte s s', n) else runPure ge s' (n + 1) limit
      | _, _ => runPure ge s' (n + 1) limit
    | none => (.stuck s, n)

/-- How a run ended. -/
inductive Outcome where
  | exit (code : Int)
  | stuck (why : String)
  | unsupported (why : String)
  | fuel
  | noinit (why : String)

structure Result where
  outcome : Outcome
  world : World
  steps : Nat
  externals : Nat
  /-- steps that needed the flat placement (O2) -/
  flat : Nat := 0

/-- Inverse of `identOfString` (6 marker bits `xI`, then the character's bits
    0..7), for diagnostics; `none` if the identifier is not of that form. -/
partial def identName (p : Positive) : Option String := do
  let rec chars (p : Positive) (acc : List Char) : Option (List Char) :=
    match p with
    | .xH => some acc.reverse
    | .xI (.xI (.xI (.xI (.xI (.xI q))))) => do
      let mut q := q
      let mut n := 0
      for i in [0:8] do
        match q with
        | .xI r => n := n + 2 ^ i; q := r
        | .xO r => q := r
        | .xH => none
      chars q (Char.ofNat n :: acc)
    | _ => none
  return String.ofList (← chars p [])

def describeStmt : Stmt → String
  | .Sskip => "Sskip" | .Sassign .. => "Sassign" | .Sset .. => "Sset"
  | .Scall .. => "Scall" | .Sbuiltin _ ef .. =>
      (match ef with
       | .EF_builtin n _ => s!"Sbuiltin {n}" | .EF_external n _ => s!"Sbuiltin(external) {n}"
       | .EF_runtime n _ => s!"Sbuiltin(runtime) {n}"
       | .EF_vload _ => "volatile load" | .EF_vstore _ => "volatile store"
       | .EF_inline_asm .. => "inline asm" | _ => "Sbuiltin")
  | .Ssequence .. => "Ssequence" | .Sifthenelse .. => "Sifthenelse"
  | .Sloop .. => "Sloop" | .Sbreak => "Sbreak" | .Scontinue => "Scontinue"
  | .Sreturn .. => "Sreturn" | .Sswitch .. => "Sswitch" | .Slabel .. => "Slabel"
  | .Sgoto .. => "Sgoto"

/-- The name of an internal function of `p`, found by its parameters and temporaries. -/
def functionName (p : Program) (f : Function) : String :=
  let key (g : Function) := (g.fn_params.map (·.1), g.fn_temps.map (·.1), g.fn_vars.map (·.1))
  let hit := p.prog_defs.find? fun (_, d) => match d with
    | .Gfun (.Internal g) => key g == key f
    | _ => false
  match hit with
  | some (i, _) => (identName i).getD "?"
  | none => "?"

def callStack (fname : Function → String) : Cont → List String
  | .Kstop => []
  | .Kseq _ k | .Kloop1 _ _ k | .Kloop2 _ _ k | .Kswitch k => callStack fname k
  | .Kcall _ f _ _ k => fname f :: callStack fname k

def showVal : Val → String
  | .Vundef => "undef" | .Vint n => s!"{Integers.Int.signed n}"
  | .Vlong n => s!"{Integers.Int64.signed n}L" | .Vptr b o => s!"ptr({b.toNat},{Integers.Ptrofs.unsigned o})"
  | .Vfloat _ => "float" | .Vsingle _ => "single"

partial def showExpr (names : Ident → String) : Expr → String
  | .Econst_int n _ => s!"{Integers.Int.signed n}" | .Econst_long n _ => s!"{Integers.Int64.signed n}L"
  | .Econst_float .. => "float" | .Econst_single .. => "single"
  | .Evar i _ => names i | .Etempvar i _ => s!"$" ++ names i
  | .Ederef a _ => s!"*({showExpr names a})" | .Eaddrof a _ => s!"&({showExpr names a})"
  | .Eunop op a _ => s!"{repr op}({showExpr names a})"
  | .Ebinop op a b _ => s!"({showExpr names a} {repr op} {showExpr names b})"
  | .Ecast a _ => s!"cast({showExpr names a})"
  | .Efield a i _ => s!"{showExpr names a}.{names i}"
  | .Esizeof .. => "sizeof" | .Ealignof .. => "alignof"

def describeStuck (names : Ident → String) (fname : Function → String := fun _ => "?")
    (ge? : Option CGenv := none) : State → String
  | .State f s k e le m =>
    let detail : String := match ge?, s with
      | some ge, .Sassign a1 a2 =>
        let lv := match doEvalLvalue ge e le m a1 with
          | some (b, o, _) => s!"lvalue ptr({b.toNat},{Integers.Ptrofs.unsigned o})"
          | none => "lvalue FAILS"
        let rv := match doEvalExpr ge e le m a2 with
          | some v => s!"rvalue {showVal v}"
          | none => s!"rvalue FAILS: {showExpr names a2}; " ++ " ".intercalate (le.elements.filterMap fun (i, v) =>
              if (showExpr names a2).contains (names i) then some s!"{names i}={showVal v}" else none)
        s!"\n  {lv}, {rv}"
      | some ge, .Sset _ a | some ge, .Sreturn (some a) | some ge, .Sifthenelse a _ _ =>
        match doEvalExpr ge e le m a with
        | some v => s!"\n  expression value {showVal v}"
        | none => s!"\n  expression FAILS: {(showExpr names a).take 400}"
      | _, _ => ""
    let bytesAt (b : Block) (o : Int) : String :=
      match Mem.loadbytes m b o 8 with
      | some vs => " ".intercalate (vs.map fun
          | .Byte c => s!"{c.toNat}" | .Undef => "U" | .Fragment v _ i => s!"F({showVal v}/{i})")
      | none => "noperm"
    let temps := le.elements.map fun (i, v) => match v with
      | .Vptr b o => s!"{names i}={showVal v}[{bytesAt b (Integers.Ptrofs.unsigned o)}]"
      | _ => s!"{names i}={showVal v}"
    s!"stuck at statement {describeStmt s} in {fname f}{detail}\n  called from: {" < ".intercalate ((callStack fname k).take 8)}\n  temps: {" ".intercalate (temps.take 30)}"
  | .Callstate (.External ef _ _ _) _ _ _ =>
    match ef with
    | .EF_external n _ => s!"call to unsupported external function {n}"
    | .EF_builtin n _ => s!"call to unsupported builtin {n}"
    | .EF_runtime n _ => s!"call to runtime helper {n}"
    | .EF_malloc => "malloc failed" | .EF_free => "invalid free"
    | _ => "stuck at external call"
  | .Callstate (.Internal _) _ _ _ => "stuck at function entry"
  | .Returnstate v .Kstop _ => s!"main returned a non-int value {repr v}"
  | .Returnstate .. => "stuck at return"

/-! ## Variadic calls (PHASES.md O1)

Clight has no rule for a call that passes variadic arguments: `eval_exprlist`
needs one parameter type per argument, so `doStep` is stuck at such an
`Scall`, and `__builtin_va_start` / `__compcert_va_int64` / … are
uninterpreted. We give them the meaning CompCert's x86-64 and AArch64 back
ends give them: the variadic arguments are stored in a fresh block, 8 bytes a
slot, `va_start` points the `va_list` at its first slot, and each `va_arg`
reads one slot and advances. The `va_list` is the array CompCert declares
(`tarray tulong 3`); we use its first 8 bytes as the cursor. -/

/-- The key of a function activation: the smallest block among its locals. -/
def activationKey (e : Env) : Option Block :=
  (e.elements.map fun (_, (b, _)) => b).foldl (fun acc b =>
    match acc with
    | none => some b
    | some a => some (if b < a then b else a)) none

def slotChunk : Val → Chunk
  | .Vint _ => .Mint32
  | .Vfloat _ => .Mfloat64
  | .Vsingle _ => .Mfloat32
  | _ => .Mint64

/-- Store the variadic arguments in a fresh block. -/
def stashVarargs (m : Mem) (vs : List Val) : Option (Block × Mem) := do
  let (m1, b) := Mem.alloc m 0 (8 * vs.length)
  let mut mm := m1
  let mut i : Nat := 0
  for v in vs do
    mm ← Mem.store (slotChunk v) mm b (8 * i) v
    i := i + 1
  return (b, mm)

/-- `doStep` is stuck at `Scall` of a variadic function with more arguments
    than parameters: evaluate the fixed arguments at the parameter types and
    the variadic ones at their own (already promoted) types. -/
def evalVarCall (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) (a : Expr) (al : List Expr) :
    Option (FunDef × List Val × List Val) := do
  let .f tyargs tyres cconv := Cop.classifyFun (typeof a) | none
  let some _ := cconv.cc_vararg | none
  if al.length ≤ tyargs.length then none
  let vf ← doEvalExpr ge e le m a
  let fixed ← doEvalExprlist ge e le m (al.take tyargs.length) tyargs
  -- the front end has already applied the default argument promotions; an
  -- array argument evaluates to its address
  let extra ← (al.drop tyargs.length).mapM fun x => doEvalExpr ge e le m x
  let fd ← Genv.findFunct ge.genv_genv vf
  if typeOfFundef fd = .Tfunction tyargs tyres cconv then some (fd, fixed, extra) else none

/-- `va_start`, `va_arg` (`__compcert_va_*`), `va_end`, `va_copy`. `k` is the
    continuation of the call, whose frame is the variadic function's. -/
def vaBuiltin (w : World) (name : String) (args : List Val) (k : Cont) (m : Mem) :
    Option (Except ExtErr ExtOut) :=
  let frameKey : Option Block := match k with
    | .Kcall _ _ e _ _ => activationKey e
    | _ => none
  let ok (r : Val) (m' : Mem) (w' : World := w) : Except ExtErr ExtOut :=
    pure { world := w', ret := r, mem := m' }
  let next (chunk : Chunk) (ap : Val) : Except ExtErr ExtOut := do
    let .Vptr apb apo := ap | throw (.ub "va_arg: va_list is not a pointer")
    let some (.Vptr vb vo) := Mem.load Mptr m apb (Integers.Ptrofs.unsigned apo)
      | throw (.ub "va_arg: va_list not initialised")
    let some v := Mem.load chunk m vb (Integers.Ptrofs.unsigned vo)
      | throw (.ub "va_arg: no more variadic arguments")
    let some m' := Mem.store Mptr m apb (Integers.Ptrofs.unsigned apo)
        (.Vptr vb (Integers.Ptrofs.add vo (Integers.Ptrofs.repr 8)))
      | throw (.ub "va_arg: va_list not writable")
    ok v m'
  match name, args with
  | "__builtin_va_start", [.Vptr apb apo] => some do
      let key ← match frameKey with
        | some key => pure key
        | none => throw (.ub "va_start outside a variadic activation")
      -- a variadic function called with no variadic argument has no block yet
      let (vb, m1, w1) := match w.va.lookup key with
        | some vb => (vb, m, w)
        | none => let (m1, vb) := Mem.alloc m 0 0; (vb, m1, { w with va := (key, vb) :: w.va })
      let some m2 := Mem.store Mptr m1 apb (Integers.Ptrofs.unsigned apo) (.Vptr vb Integers.Ptrofs.zero)
        | throw (.ub "va_start: va_list not writable")
      ok .Vundef m2 w1
  | "__builtin_va_end", [_] => some (ok .Vundef m)
  | "__builtin_va_copy", [.Vptr db dofs, .Vptr sb sofs] => some do
      let some v := Mem.load Mptr m sb (Integers.Ptrofs.unsigned sofs) | throw (.ub "va_copy: source")
      let some m' := Mem.store Mptr m db (Integers.Ptrofs.unsigned dofs) v | throw (.ub "va_copy: dest")
      ok .Vundef m'
  | "__compcert_va_int32", [ap] => some (next .Mint32 ap)
  | "__compcert_va_int64", [ap] => some (next .Mint64 ap)
  | "__compcert_va_float64", [ap] => some (next .Mfloat64 ap)
  | _, _ => none

/-- Run program `p` from `main` with the external model. `args` are main's arguments. -/
def runProgram (p : Program) (limit : Nat) (w0 : World := {}) (traceFlat : Bool := false) : Result := Id.run do
  let ge := p.globalenv
  let fail (o : Outcome) (w : World) (n e : Nat) : Result := ⟨o, w, n, e, 0⟩
  let some m0 := p.initMem | return fail (.noinit "global initialisation failed") w0 0 0
  let some b := Genv.findSymbol ge.genv_genv p.prog_main | return fail (.noinit "no main") w0 0 0
  let some f := Genv.findFunctPtr ge.genv_genv b | return fail (.noinit "main is not a function") w0 0 0
  let args : List Val ← match typeOfFundef f with
    | .Tfunction [] _ _ => pure []
    | .Tfunction [_, _] _ _ => pure [.Vint 0, .Vlong 0]
    | _ => return fail (.noinit "unsupported type for main") w0 0 0
  let mut s : State := .Callstate f args .Kstop m0
  let mut w := w0
  let mut total := 0
  let mut ext := 0
  let mut flat := 0
  let names : Ident → String := fun i => (identName i).getD s!"t'{i.toNat - 127}"
  repeat
    let (stop, n) := runPure ge s 0 (if limit == 0 then 0 else limit - total)
    total := total + n
    match stop with
    | .done r => return ⟨.exit (Integers.Int.signed r), w, total, ext, flat⟩
    | .fuel _ => return ⟨.fuel, w, total, ext, flat⟩
    | .undefByte st st' =>
      total := total + 1
      match st with
      | .State f stmt k e le m =>
        match flatStmt ge e le m stmt with
        | some stmt' =>
          match doStep ge (.State f stmt' k e le m) with
          | some (_, s') => flat := flat + 1; s := s'
          | none => s := st'
        | none => s := st'
      | _ => s := st'
    | .stuck st =>
      match st with
      | .Callstate (.External ef _ _ _) vargs k m =>
        let name := match ef with
          | .EF_external n _ | .EF_builtin n _ | .EF_runtime n _ => n
          | _ => ""
        let call := match vaBuiltin w name vargs k m with
          | some r => some r
          | none => match ef with
            | .EF_external .. => callExternal w name vargs m
            | _ => none
        match call with
        | none => return ⟨.stuck (describeStuck names (functionName p) (some ge) st), w, total, ext, flat⟩
        | some (.error (.ub msg)) => return ⟨.stuck s!"{name}: {msg}", w, total, ext, flat⟩
        | some (.error (.unsupported msg)) => return ⟨.unsupported s!"{name}: {msg}", w, total, ext, flat⟩
        | some (.ok r) =>
          w := r.world
          total := total + 1
          ext := ext + 1
          if let some c := w.exited then return ⟨.exit c, w, total, ext, flat⟩
          s := .Returnstate r.ret k r.mem
      -- volatile access (clightgen -normalize makes them builtins): for a block
      -- that is not a volatile global, `VolatileLoad.nonvol`/`VolatileStore.nonvol`
      -- of CCLib's `Events`: a plain load/store with an empty trace
      | .State f (.Sbuiltin optid (.EF_vload chunk) tyargs al) k e le m =>
        match doEvalExprlist ge e le m al tyargs with
        | some [.Vptr b ofs] =>
          if Genv.blockIsVolatile ge.genv_genv b then
            return ⟨.unsupported "load from a volatile global", w, total, ext, flat⟩
          match Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) with
          | some v => total := total + 1; s := .State f .Sskip k e (setOpttemp optid v le) m
          | none => return ⟨.stuck "volatile load: no permission", w, total, ext, flat⟩
        | _ => return ⟨.stuck "volatile load: bad address", w, total, ext, flat⟩
      | .State f (.Sbuiltin optid (.EF_vstore chunk) tyargs al) k e le m =>
        match doEvalExprlist ge e le m al tyargs with
        | some [.Vptr b ofs, v] =>
          if Genv.blockIsVolatile ge.genv_genv b then
            return ⟨.unsupported "store to a volatile global", w, total, ext, flat⟩
          match Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v with
          | some m' => total := total + 1; s := .State f .Sskip k e (setOpttemp optid .Vundef le) m'
          | none => return ⟨.stuck "volatile store: no permission", w, total, ext, flat⟩
        | _ => return ⟨.stuck "volatile store: bad address", w, total, ext, flat⟩
      | .State f (.Scall optid a al) k e le m =>
        match evalVarCall ge e le m a al with
        | none => return ⟨.stuck (describeStuck names (functionName p) (some ge) st), w, total, ext, flat⟩
        | some (.External (.EF_external name _) _ _ _, fixed, extra) =>
          -- a variadic libc function (fcntl): the model sees all arguments
          match callExternal w name (fixed ++ extra) m with
          | none => return ⟨.stuck s!"call to unsupported external function {name}", w, total, ext, flat⟩
          | some (.error (.ub msg)) => return ⟨.stuck s!"{name}: {msg}", w, total, ext, flat⟩
          | some (.error (.unsupported msg)) => return ⟨.unsupported s!"{name}: {msg}", w, total, ext, flat⟩
          | some (.ok r) =>
            w := r.world; total := total + 1; ext := ext + 1
            s := .State f .Sskip k e (setOpttemp optid r.ret le) r.mem
        | some (fd@(.Internal _), fixed, extra) =>
          let some (vb, m1) := stashVarargs m extra
            | return ⟨.stuck "cannot store variadic arguments", w, total, ext, flat⟩
          -- the call step, then function entry, so that the activation is known
          match doStep ge (.Callstate fd fixed (.Kcall optid f e le k) m1) with
          | some (_, s'@(.State _ _ _ e' _ _)) =>
            if let some key := activationKey e' then w := { w with va := (key, vb) :: w.va }
            total := total + 2
            s := s'
          | _ => return ⟨.stuck "function entry of a variadic function failed", w, total, ext, flat⟩
        | some _ => return ⟨.stuck (describeStuck names (functionName p) (some ge) st), w, total, ext, flat⟩
      | .State f stmt k e le m =>
        match flatStmt ge e le m stmt with
        | some stmt' =>
          match doStep ge (.State f stmt' k e le m) with
          | some (_, s') =>
            flat := flat + 1; total := total + 1; s := s'
            if traceFlat then w := { w with err := w.err ++ s!"[flat] {functionName p f} {showExpr names (match stmt' with | .Sifthenelse a _ _ => a | .Sset _ a => a | .Sreturn (some a) => a | _ => .Econst_int 0 Ty.Tvoid)}\n".toUTF8 }
          | none => return ⟨.stuck (describeStuck names (functionName p) (some ge) st), w, total, ext, flat⟩
        | none => return ⟨.stuck (describeStuck names (functionName p) (some ge) st), w, total, ext, flat⟩
      | _ => return ⟨.stuck (describeStuck names (functionName p) (some ge) st), w, total, ext, flat⟩
  return ⟨.fuel, w, total, ext, flat⟩

end Run
