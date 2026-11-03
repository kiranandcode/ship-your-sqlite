/-
  Date and time functions (https://sqlite.org/lang_datefunc.html): date, time,
  datetime, julianday, unixepoch, strftime, timediff, and CURRENT_*.
  STUB: to be filled (see PHASES.md "Phase 2 lanes").
-/
import Sql.Db

namespace Sql.DateTime

/-- The clock the semantics reads for 'now' (a parameter of the semantics):
    milliseconds since the Unix epoch. -/
structure Clock where
  unixMs : Int := 0

/-- `none` if `name` is not a date/time function. -/
def scalar? (_clock : Clock) (_name : String) (_args : List Value) : Option (Except Err Value) := none

end Sql.DateTime
