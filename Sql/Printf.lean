/-
  SQLite's printf (`sqlite3_str_vappendf`): the SQL functions `printf()` and
  `format()`, and the decimal conversion `round()` goes through.
  STUB: to be filled (see PHASES.md "Phase 2 lanes").
-/
import Sql.Db

namespace Sql.Printf

/-- `printf(fmt, args…)` / `format(…)`: `none` if this module does not implement `name`. -/
def scalar? (_name : String) (_args : List Value) : Option (Except Err Value) := none

/-- `round(r, n)` as SQLite computes it (through `%!.*f`); `none` until implemented. -/
def round? (_r : Float) (_n : Int) : Option Float := none

/-- `quote()` of a REAL (SQLite: `%!0.15g`, or `%!0.20e` when that does not
    read back as the same double); `none` until implemented. -/
def quoteReal? (_r : Float) : Option String := none

end Sql.Printf
