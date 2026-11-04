/-
  The refinement theorem (Phase 3.1), stated: SQLite's Clight program, run on
  a script under the extended Clight semantics (`Run.StepX`: clean's step plus
  the three extensions of TRUST.md), terminates, and what it prints is an
  output of the script in the denotational semantics (`Sql.Den.Derives`:
  membership in `Sql.Den.runScript`, Phase 2.6).

  Not proved: `SqliteRefines_Statement` is a `Prop` (CLAUDE.md law 2), listed
  under Obligations in PHASES.md.
-/
import Run.StepX
import Sql.Den.Exec

namespace Spec

open Sql

/-- The non-blank tokens of a script. -/
def tokens (script : ByteArray) : List Token :=
  (tokenize script).toList.filter (·.tk != .space)

def isKw (k : String) (t : Token) : Bool := t.tk == .kw k

/-- The text of a token. -/
def text (script : ByteArray) (t : Token) : ByteArray := script.extract t.start t.stop

/-- The statements of a script, as lists of non-blank tokens (split at `;`). -/
def statements (script : ByteArray) : List (List Token) :=
  (tokens script).splitOnP (fun t => t.tk == .op "SEMI")

/-- Every `ATTACH [DATABASE] x` names an in-memory database: `x` is the
    string literal `':memory:'` or `''`. -/
def attachesMemoryOnly (script : ByteArray) : Prop :=
  ∀ s ∈ statements script, ∀ i, (s[i]?.map (isKw "ATTACH")) = some true →
      let rest := (s.drop (i + 1)).dropWhile (isKw "DATABASE")
      ∃ t ∈ rest.head?.toList, t.tk == .str ∧
        (text script t == "':memory:'".toUTF8 ∨ text script t == "''".toUTF8)

/-- The premises under which the theorem is claimed, each a named field with
    what removes it. -/
structure Admissible (script : ByteArray) : Prop where
  /-- EXPLAIN and EXPLAIN QUERY PLAN print SQLite's bytecode and plan, which
      the SQL semantics does not model. Pending Kiran's decision 2 (cove
      report): in scope (then the semantics models VDBE listings) or out of
      scope via this premise. -/
  noExplain : ∀ t ∈ tokens script, isKw "EXPLAIN" t = false
  /-- The external model has no file system (`open` fails with ENOENT), so
      only in-memory databases can be attached. Removed by the file system
      model of Phase 1.5. -/
  memoryDatabasesOnly : attachesMemoryOnly script
  /-- VACUUM (and VACUUM INTO a file) is not modelled by the semantics
      (PHASES.md, Phase 2 gaps). -/
  noVacuum : ∀ t ∈ tokens script, isKw "VACUUM" t = false
  /-- SQLite's parser limits ("Recursion limit", "Expression tree is too large
      (maximum depth 1000)") are not modelled (Gaps); statements of at most 500
      tokens stay below both. Removed when the semantics models the limits. -/
  statementSize : ∀ s ∈ statements script, s.length ≤ 500

/-- The refinement: on an admissible script, the program terminates, and its
    output is derived by the SQL semantics. `p` is the Clight program
    `clightgen -lean` produces from `sqlite3.c` + `c/driver.c`
    (`Sqlprog.prog`, generated, not committed); it is a parameter so that the
    statement does not import the 47 MB export. -/
structure Refines (p : CC.Program) : Prop where
  terminates : ∀ script, Admissible script → ∃ out, Run.ClightRuns p script out
  sound : ∀ script, Admissible script → ∀ out, Run.ClightRuns p script out → Den.Derives script out

/-- Phase 3's theorem, about the export. Known false as stated on the scripts
    of BUGS.md #3 (a NaN converted to an integer: the Clight run is stuck, so
    `terminates` fails) until Kiran's decision 1: a fourth extension (x86's
    `cvttsd2si`) or a premise excluding those conversions. -/
def SqliteRefines_Statement (p : CC.Program) : Prop := Refines p

end Spec
