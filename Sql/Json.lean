/-
  JSON functions (https://sqlite.org/json1.html), as SQLite 3.54.1's json.c
  implements them: the scalar functions, the `->` and `->>` operators, the
  aggregates json_group_array/json_group_object (and jsonb_ variants), and
  the table-valued json_each/json_tree (and jsonb_ variants).

  The work is in `Sql/Json/` (Blob: JSONB and text; Edit: lookup and
  in-place edits; Funcs: the SQL functions). This file is the interface the
  evaluator calls.

  ## The JSON subtype

  A JSON function's text result carries the subtype 'J'; a JSON function
  receiving a subtyped text embeds it as JSON instead of quoting it as a
  string. In SQLite the subtype lives on the value (a VDBE register), so
  which expressions keep it is a dynamic matter. Checked against the oracle
  (tests/sem/json_subtype.sql), the subtype survives:
    * a direct call of json, json_array, json_object, json_quote, json_set,
      json_insert, json_replace, json_remove, json_patch, json_array_insert,
      json_extract (only when the result is an array or object; always with
      more than one path), json_group_array, json_group_object, and `->`;
    * parentheses, `CASE` (the branch taken), `coalesce`/`ifnull`/`iif`/
      `nullif`, multi-argument `min`/`max`, `likely`/`unlikely`/
      `likelihood`, unary `+`, `COLLATE`, `CAST(… AS TEXT)`;
    * the `value` column of json_each/json_tree for arrays and objects.
  It is lost through a subquery (scalar or in FROM), a CTE or view, a table
  column, `||`, `printf`, other scalar functions, `->>`, and through the
  result of an aggregate read back from a subquery.

  `exprIsJson` decides this statically: a JSON-producing call or `->` is
  JSON; the wrappers above are JSON when one of their result branches is.
  Two value-dependent cases are approximated: `json_extract` of a scalar
  (no subtype in SQLite) and mixed branches (`coalesce(json(x), 'text')`).
  To limit the damage, a text value flagged as JSON is embedded raw only if
  it is canonical JSON (`Funcs.subtypeOk`); so `json_extract('["a"]','$[0]')`
  nested in json_array still gives `["a"]`, but an extracted *string* whose
  content is itself canonical JSON (e.g. `"123"`) is embedded as a number.
  Not modelled: the json_each `value` column's subtype (a column reference
  carries no expression information).

  The precise interface for an evaluator that carries subtypes on values is
  `scalarST?`/`aggregateST?`/`tableFnST?` (results with their subtype), and
  `scalarCached` threads json.c's per-statement parse cache (`Funcs.Cache`).
-/
import Sql.Ast
import Sql.Db
import Sql.Json.Funcs

namespace Sql.Json

/-- Functions whose result carries the JSON subtype. -/
def jsonProducers : List String :=
  ["json", "json_array", "json_array_insert", "json_extract", "json_insert", "json_object",
   "json_patch", "json_quote", "json_remove", "json_replace", "json_set",
   "json_group_array", "json_group_object"]

/-- Is the value of this expression a JSON-subtyped value when passed directly
    as an argument (a call to a JSON function, or `->`)? See the file comment. -/
partial def exprIsJson : Expr → Bool
  | .call name _ args _ _ _ over =>
    let n := name.toLower
    if over.isSome then false
    else if jsonProducers.contains n then true
    else match n with
      | "nullif" | "likely" | "unlikely" | "likelihood" => (args.head?.map exprIsJson).getD false
      | "iif" | "if" =>
        -- iif(c1, v1, c2, v2, …, else): the values are at odd positions and the last
        let idx := List.range args.length
        (idx.zip args).any fun (i, a) => (i % 2 == 1 || (args.length % 2 == 1 && i + 1 == args.length)) && exprIsJson a
      | "coalesce" | "ifnull" => args.any exprIsJson
      | "min" | "max" => args.length ≥ 2 && args.any exprIsJson
      | _ => false
  | .binop .ptr _ _ => true
  | .case_ _ whens else_ => whens.any (fun (_, v) => exprIsJson v) || (else_.map exprIsJson).getD false
  | .unop .pos e => exprIsJson e
  | .collate e _ => exprIsJson e
  | .cast e _ => exprIsJson e
  | _ => false

/-- A scalar call with an explicit parse cache: the result (NULL as `.null`)
    with its subtype, and the cache after the call. -/
def scalarCached (cache : Cache) (name : String) (args : List (Value × Bool)) :
    Option (Except Err ((Value × Bool) × Cache)) :=
  (scalarF name args).map fun m =>
    (m.run cache).map fun (o, c) => (o.getD (.null, false), c)

/-- Scalar JSON functions with the subtype of the result (fresh cache). -/
def scalarST? (name : String) (args : List (Value × Bool)) : Option (Except Err (Value × Bool)) :=
  (scalarCached {} name args).map (·.map (·.1))

/-- Scalar JSON functions and `->`/`->>` (names "->", "->>"). `args` pairs each
    argument with whether it carries the JSON subtype. -/
def scalar? (name : String) (args : List (Value × Bool)) : Option (Except Err Value) :=
  (scalarST? name args).map (·.map (·.1))

/-- Aggregates with the subtype of the result. -/
def aggregateST? (name : String) (rows : List (List (Value × Bool))) : Option (Except Err (Value × Bool)) :=
  (aggregateF name rows).map fun m => m.run' {}

/-- Aggregates: the argument lists of the group's rows, in order. -/
def aggregate? (name : String) (rows : List (List (Value × Bool))) : Option (Except Err Value) :=
  (aggregateST? name rows).map (·.map (·.1))

def tableFns : List String := ["json_each", "json_tree", "jsonb_each", "jsonb_tree"]

/-- Table-valued functions with all ten columns (the last two, `json` and
    `root`, are HIDDEN in SQLite) and the subtype of `value` per row. -/
def tableFnST? (name : String) (args : List (Value × Bool)) :
    Option (Except Err (List String × List (List Value × Bool))) :=
  if tableFns.contains name then some ((eachRows name args).map (eachColumns, ·)) else none

/-- Table-valued functions: column names and rows. Only the eight visible
    columns are returned, so that `*` expands as in SQLite (the evaluator has
    no notion of hidden columns of a table-valued function yet). -/
def tableFn? (name : String) (args : List (Value × Bool)) : Option (Except Err (List String × List (List Value))) :=
  (tableFnST? name args).map fun r => r.map fun (cols, rows) =>
    (cols.take 8, rows.map fun (vs, _) => vs.take 8)

end Sql.Json
