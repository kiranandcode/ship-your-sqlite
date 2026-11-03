/-
  JSON functions (https://sqlite.org/json1.html): scalar functions, the `->`
  and `->>` operators, the aggregates json_group_array/json_group_object (and
  jsonb_ variants), and the table-valued json_each/json_tree.
  STUB: to be filled (see PHASES.md "Phase 2 lanes").
-/
import Sql.Ast
import Sql.Db

namespace Sql.Json

/-- Is the value of this expression a JSON-subtyped value when passed directly
    as an argument (a call to a JSON function, or `->`)? -/
def exprIsJson (_e : Expr) : Bool := false

/-- Scalar JSON functions and `->`/`->>` (names "->", "->>"). `args` pairs each
    argument with whether it carries the JSON subtype. -/
def scalar? (_name : String) (_args : List (Value × Bool)) : Option (Except Err Value) := none

/-- Aggregates: the argument lists of the group's rows, in order. -/
def aggregate? (_name : String) (_rows : List (List (Value × Bool))) : Option (Except Err Value) := none

/-- Table-valued functions: column names and rows. -/
def tableFn? (_name : String) (_args : List (Value × Bool)) : Option (Except Err (List String × List (List Value))) := none

end Sql.Json
