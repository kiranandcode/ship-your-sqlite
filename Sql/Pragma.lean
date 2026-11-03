/-
  PRAGMA statements (https://sqlite.org/pragma.html) as SQLite 3.54.1's
  pragma.c implements them, for the D7 build on an in-memory database.
  STUB: to be filled (see PHASES.md "Phase 2 lanes").
-/
import Sql.Db

namespace Sql.Pragma

/-- `PRAGMA [schema.]name [= arg | (arg)]` on database state `db`. `arg` is the
    argument as SQLite sees it: its text (a bare identifier or keyword is its
    name). Returns the new state and the result rows, or an error; `none` if
    this module does not implement `name` (the executor's fallback runs). -/
def run (_db : Db) (_schema : Option String) (_name : String) (_arg : Option Value) (_call : Bool) :
    Option (Except Err (Db × Array (Array Value))) := none

end Sql.Pragma
