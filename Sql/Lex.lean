/-
  The SQL lexer: SQLite's tokenizer (https://sqlite.org/lang.html, and the
  token classes of its grammar). Works on the script's bytes (UTF-8), as
  SQLite does.
-/
import Sql.Keywords

namespace Sql

/-- Token classes. Keywords carry SQLite's class name (`SELECT`, `JOIN_KW`, …). -/
inductive Tk where
  | space                    -- whitespace and comments
  | id                       -- identifier, possibly quoted ("x", `x`, [x])
  | str                      -- 'string'
  | integer | float | qnumber   -- numbers (qnumber: with '_' separators)
  | blob                     -- x'0A'
  | variable                 -- ?, ?NNN, :aaa, @aaa, $aaa
  | kw (cls : String)        -- a keyword, with its class
  | op (name : String)       -- LP RP SEMI COMMA DOT PLUS MINUS STAR SLASH REM EQ NE LT LE GT GE
                             -- LSHIFT RSHIFT BITAND BITOR BITNOT CONCAT PTR
  | illegal
  deriving BEq, Repr, Inhabited

/-- A token: class and byte range `[start, stop)` of the script. -/
structure Token where
  tk : Tk
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

def isSpaceB (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 12 || c == 13
def isDigitB (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isHexB (c : UInt8) : Bool := isDigitB c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
def isAlphaB (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
/-- identifier characters: letters, digits, `_`, `$`, and every byte ≥ 0x80 -/
def isIdCharB (c : UInt8) : Bool := isAlphaB c || isDigitB c || c == 95 || c == 36 || c ≥ 128
def isIdStartB (c : UInt8) : Bool := isAlphaB c || c == 95 || c ≥ 128

def upperB (c : UInt8) : UInt8 := if 97 ≤ c && c ≤ 122 then c - 32 else c

def keywordClass (word : ByteArray) : Option String :=
  if word.size > 17 then none else
  let up := String.fromUTF8! (ByteArray.mk (word.data.map upperB))
  (keywords.find? (·.1 == up)).map (·.2)

/-! Scanning loops of the lexer, as recursion on the bytes left. -/
namespace Lex

/-- The first index `≥ j` of `z` whose byte fails `p`, or the end of `z`. -/
def scanWhile (z : ByteArray) (p : UInt8 → Bool) (j : Nat) : Nat :=
  if h : j < z.size then (if p z[j] then scanWhile z p (j + 1) else j) else j
termination_by z.size - j

/-- The end of a block comment whose body starts at `j`: just after the
    closing `*/`, or the end of `z` when it is unterminated. -/
def commentEnd (z : ByteArray) (j : Nat) : Nat :=
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  if h : j ≥ n then n
  else if at_ j == 42 && at_ (j+1) == 47 then j + 2
  else commentEnd z (j + 1)
termination_by z.size - j

/-- The end of a quoted token delimited by `q` whose body starts at `j`
    (a doubled delimiter stands for itself): just after the closing
    delimiter, or `none` when it is unterminated. -/
def quotedEnd (z : ByteArray) (q : UInt8) (j : Nat) : Option Nat :=
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  if h : j ≥ n then none
  else if at_ j == q then (if at_ (j+1) == q then quotedEnd z q (j + 2) else some (j + 1))
  else quotedEnd z q (j + 1)
termination_by z.size - j

/-- The end of the name of a variable `$AAAA @AAAA :AAAA #AAAA` (lead byte
    `c` at `i`), scanning from `j`: identifier characters, and for `$` also
    TCL's `::` separators and one `(…)` suffix. -/
def varEnd (z : ByteArray) (c : UInt8) (i j : Nat) : Nat :=
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  -- past the end every test below fails (`at_` is 0 there)
  if h : j < n then
    if isIdCharB (at_ j) then varEnd z c i (j + 1)
    else if c == 36 && at_ j == 58 && at_ (j+1) == 58 then varEnd z c i (j + 2)
    else if c == 36 && at_ j == 40 && j > i + 1 then
      let k := scanWhile z (fun b => b != 41 && !isSpaceB b) (j + 1)
      if k < n && at_ k == 41 then k + 1 else j
    else j
  else j
termination_by z.size - j

/-- Decimal (or, with `hex`, hexadecimal) digits from `j`, with `_`
    separators between two digits (the token starts at `i`): the index after
    them and whether a separator was seen. -/
def digitsU (z : ByteArray) (i : Nat) (hex : Bool) (j : Nat) (sep : Bool) : Nat × Bool :=
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  let d := at_ j
  -- past the end `d` is 0, neither a digit nor `_`
  if h : j < n then
    if (if hex then isHexB d else isDigitB d) then digitsU z i hex (j + 1) sep
    else if d == 95 && j > i && (if hex then isHexB (at_ (j-1)) && isHexB (at_ (j+1))
                                 else isDigitB (at_ (j-1)) && isDigitB (at_ (j+1))) then
      digitsU z i hex (j + 1) true
    else (j, sep)
  else (j, sep)
termination_by z.size - j

end Lex

/-- Length and class of the token starting at `i` of `z` (`i < z.size`). -/
def tokenAt (z : ByteArray) (i : Nat) : Nat × Tk :=
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  let c := at_ i
  let scanWhile (p : UInt8 → Bool) (j : Nat) : Nat := Lex.scanWhile z p j
  if isSpaceB c then (scanWhile isSpaceB i - i, .space)
  else if c == 45 then -- '-'
    if at_ (i+1) == 45 then
      let j := scanWhile (· != 10) (i + 2)
      (j - i, .space)
    else if at_ (i+1) == 62 then
      (if at_ (i+2) == 62 then 3 else 2, .op "PTR")
    else (1, .op "MINUS")
  else if c == 40 then (1, .op "LP")
  else if c == 41 then (1, .op "RP")
  else if c == 59 then (1, .op "SEMI")
  else if c == 43 then (1, .op "PLUS")
  else if c == 42 then (1, .op "STAR")
  else if c == 47 then -- '/'
    if at_ (i+1) != 42 then (1, .op "SLASH") else
    (Lex.commentEnd z (i + 2) - i, .space)
  else if c == 37 then (1, .op "REM")
  else if c == 61 then (if at_ (i+1) == 61 then 2 else 1, .op "EQ")
  else if c == 60 then
    let d := at_ (i+1)
    if d == 61 then (2, .op "LE") else if d == 62 then (2, .op "NE")
    else if d == 60 then (2, .op "LSHIFT") else (1, .op "LT")
  else if c == 62 then
    let d := at_ (i+1)
    if d == 61 then (2, .op "GE") else if d == 62 then (2, .op "RSHIFT") else (1, .op "GT")
  else if c == 33 then (if at_ (i+1) == 61 then (2, .op "NE") else (1, .illegal))
  else if c == 124 then (if at_ (i+1) == 124 then (2, .op "CONCAT") else (1, .op "BITOR"))
  else if c == 44 then (1, .op "COMMA")
  else if c == 38 then (1, .op "BITAND")
  else if c == 126 then (1, .op "BITNOT")
  else if c == 39 || c == 34 || c == 96 then
    -- quoted: a doubled delimiter stands for itself
    match Lex.quotedEnd z c (i + 1) with
    | some j => (j - i, if c == 39 then .str else .id)
    | none => (n - i, .illegal)
  else if c == 46 then
    if isDigitB (at_ (i+1)) then numberAt z i else (1, .op "DOT")
  else if isDigitB c then numberAt z i
  else if c == 91 then -- '['
    let j := scanWhile (· != 93) (i + 1)
    if j < n then (j + 1 - i, .id) else (n - i, .illegal)
  else if c == 63 then (scanWhile isDigitB (i + 1) - i, .variable)
  else if c == 36 || c == 64 || c == 58 || c == 35 then
    -- $AAAA @AAAA :AAAA #AAAA ($ also takes TCL's ::name and (…) suffixes)
    let j := Lex.varEnd z c i (i + 1)
    if j == i + 1 then (1, .illegal) else (j - i, .variable)
  else if (c == 120 || c == 88) && at_ (i+1) == 39 then
    let j := scanWhile isHexB (i + 2)
    if at_ j != 39 || (j - i - 2) % 2 == 1 then
      let k := scanWhile (fun b => b != 39) j
      (min n (k + 1) - i, .illegal)
    else (j + 1 - i, .blob)
  else if isIdStartB c then
    let j := scanWhile isIdCharB (i + 1)
    match keywordClass (z.extract i j) with
    | some cls => (j - i, .kw cls)
    | none => (j - i, .id)
  else (1, .illegal)
where
  numberAt (z : ByteArray) (i : Nat) : Nat × Tk :=
    let n := z.size
    let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
    let digitsU (j : Nat) (hex : Bool) : Nat × Bool := Lex.digitsU z i hex j false
    if at_ i == 48 && (at_ (i+1) == 120 || at_ (i+1) == 88) && isHexB (at_ (i+2)) then
      let (j, sep) := digitsU (i + 2) true
      if isIdCharB (at_ j) then (j + 1 - i, .illegal)
      else (j - i, if sep then .qnumber else .integer)
    else
      let (j, sep1) := digitsU i false
      let (j, isF, sep2) :=
        if at_ j == 46 then
          let (k, s) := digitsU (j + 1) false
          (k, true, s)
        else (j, false, false)
      let (j, isF, sep3) :=
        if (at_ j == 101 || at_ j == 69) &&
           (isDigitB (at_ (j+1)) || ((at_ (j+1) == 43 || at_ (j+1) == 45) && isDigitB (at_ (j+2)))) then
          let (k, s) := digitsU (j + (if isDigitB (at_ (j+1)) then 1 else 2)) false
          (k, true, s)
        else (j, isF, false)
      if isIdCharB (at_ j) then
        -- "1abc": the token runs to the end of the identifier characters
        (Lex.scanWhile z isIdCharB j - i, .illegal)
      else (j - i, if sep1 || sep2 || sep3 then .qnumber else if isF then .float else .integer)

/-- The tokens of `z` from byte `i`, without whitespace/comments. -/
def tokenize (z : ByteArray) (i : Nat := 0) : Array Token := go i #[]
where
  go (i : Nat) (out : Array Token) : Array Token :=
    if _h : i < z.size then
      let r := tokenAt z i
      let len := max r.1 1
      go (i + len) (if r.2 != .space then out.push ⟨r.2, i, i + len⟩ else out)
    else out
  termination_by z.size - i

end Sql
