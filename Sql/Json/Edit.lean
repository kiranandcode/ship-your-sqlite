/-
  Searching and editing JSONB in place (json.c: `jsonLookupStep`,
  `jsonBlobEdit`, `jsonBlobOverwrite`, `jsonBlobChangePayloadSize`,
  `jsonAfterEditSizeAdjust`, `jsonCreateEditSubstructure`, `jsonMergePatch`).
  Edits are byte-exact: SQLite sometimes keeps a non-minimal size header
  (`jsonBlobOverwrite` widens the header of a replacement instead of moving
  the rest of the blob), and that is observable in `jsonb_*` results.
-/
import Sql.Json.Blob

namespace Sql.Json

/-- A `JsonParse`: the blob and the search/edit state. -/
structure JP where
  b : ByteArray
  delta : Int := 0
  /-- 0 none, 1 DEL, 2 REPL, 3 INS, 4 SET, 5 AINS -/
  eEdit : Nat := 0
  ins : ByteArray := .empty
  iLabel : Nat := 0
  /-- u16 -/
  iDepth : Nat := 0
  nonstd : Bool := false
  deriving Inhabited

def eDEL : Nat := 1
def eREPL : Nat := 2
def eINS : Nat := 3
def eSET : Nat := 4
def eAINS : Nat := 5

def lERROR : Nat := 0xffffffff
def lNOTFOUND : Nat := 0xfffffffe
def lNOTARRAY : Nat := 0xfffffffd
def lTOODEEP : Nat := 0xfffffffc
def lPATHERROR : Nat := 0xfffffffb
def isLookupErr (x : Nat) : Bool := x ≥ lPATHERROR

def JP.psize (p : JP) (i : Nat) : Nat × Nat := payloadSize p.b p.delta i
def JP.typ (p : JP) (i : Nat) : UInt8 := (bat p.b i) &&& 0x0f

/-- Overwrite bytes at `i`. -/
def writeAt (b : ByteArray) (i : Nat) (src : ByteArray) : ByteArray :=
  b.extract 0 i ++ src ++ b.extract (i + src.size) b.size

/-- `jsonBlobOverwrite`: `aIns` with its header widened by `d` bytes. -/
def overwrite (aIns : ByteArray) (d : Nat) : Option ByteArray := Id.run do
  let c := bat aIns 0
  if c &&& 0x0f ≤ 2 then return none
  let (i, szHdr) ← match (c >>> 4).toNat with
    | 12 => if (1 <<< d) &&& 0x8a == 0 then return none else pure (d + 2, 2)
    | 13 => if d != 2 && d != 6 then return none else pure (d + 3, 3)
    | 14 => if d != 4 then return none else pure (9, 5)
    | 15 => return none
    | _ => if (1 <<< d) &&& 0x116 == 0 then return none else pure (d + 1, 1)
  let aType : Nat → UInt8 := fun k => match k with
    | 2 => 0xc0 | 3 => 0xd0 | 5 => 0xe0 | 9 => 0xf0 | _ => 0
  let szPayload := aIns.size - szHdr
  let mut hdr := ByteArray.empty.push ((c &&& 0x0f) ||| aType i)
  -- bytes 1..i-1: szPayload big-endian
  for k in [1:i] do
    let shift := 8 * (i - 1 - k)
    hdr := hdr.push ((szPayload >>> shift) &&& 0xff).toUInt8
  return some (hdr ++ aIns.extract szHdr aIns.size)

/-- `jsonBlobEdit`: remove `nDel` bytes at `iDel` and insert `ins` (or
    `nIns` zero bytes to be filled by the caller when `ins` is `none`). -/
def JP.edit (p : JP) (iDel nDel : Nat) (ins : Option ByteArray) (nIns : Nat) : JP :=
  let d : Int := (nIns : Int) - nDel
  let ow : Option ByteArray :=
    if d < 0 && d ≥ -8 then ins.bind fun a => overwrite a (-d).toNat else none
  match ow with
  | some bytes => { p with b := writeAt p.b iDel bytes }
  | none =>
    let content := match ins with
      | some a => a
      | none => ByteArray.mk (Array.replicate nIns 0)
    { p with b := p.b.extract 0 iDel ++ content ++ p.b.extract (iDel + nDel) p.b.size,
             delta := p.delta + d }

/-- `jsonBlobChangePayloadSize`: rewrite the size field of node `i`;
    returns the change in header size. -/
def JP.changePayloadSize (p : JP) (i szPayload : Nat) : JP × Int :=
  let a0 := bat p.b i
  let szType := (a0 >>> 4).toNat
  let nExtra : Nat := if szType ≤ 11 then 0 else if szType == 12 then 1 else if szType == 13 then 2 else if szType == 14 then 4 else 8
  let nNeeded : Nat := if szPayload ≤ 11 then 0 else if szPayload ≤ 0xff then 1 else if szPayload ≤ 0xffff then 2 else 4
  let delta : Int := (nNeeded : Int) - nExtra
  let hdr := header (a0 &&& 0x0f) szPayload
  -- header(...) has exactly 1 + nNeeded bytes
  let b := p.b.extract 0 i ++ hdr ++ p.b.extract (i + 1 + nExtra) p.b.size
  ({ p with b }, delta)

/-- `jsonAfterEditSizeAdjust` -/
def JP.afterEditSizeAdjust (p : JP) (iRoot : Nat) : JP :=
  let (_, sz) := payloadSizeRaw p.b iRoot
  let sz : Int := (sz : Int) + p.delta
  let (p, d) := p.changePayloadSize iRoot sz.toNat
  { p with delta := p.delta + d }

def JP.adjustIf (p : JP) (iRoot : Nat) : JP := if p.delta != 0 then p.afterEditSizeAdjust iRoot else p

/-- `jsonbArrayCount` -/
def JP.arrayCount (p : JP) (iRoot : Nat) : Nat := Id.run do
  let (n0, sz0) := p.psize iRoot
  let iEnd := iRoot + n0 + sz0
  let mut k := 0
  let mut i := iRoot + n0
  let mut n := n0
  while n > 0 && i < iEnd do
    let (n', sz') := p.psize i
    n := n'
    i := i + sz' + n'
    k := k + 1
  return k

/-- Does the path from `pi` end with `]` (`sqlite3_strglob("*]", …)==0`)? -/
def endsWithBracket (path : ByteArray) (pi : Nat) : Bool :=
  let s := cstr (path.extract pi path.size)
  s.size > 0 && bat s (s.size - 1) == 93

mutual
/-- `jsonLookupStep`: the index of the node at `path[pi..]` below `iRoot`,
    or an error code; performs the edit `p.eEdit` on the way. -/
partial def lookupStep (p : JP) (iRoot : Nat) (path : ByteArray) (pi : Nat) (iLabel : Nat) : Nat × JP := Id.run do
  let mut p := p
  if bat path pi == 0 then
    if p.eEdit != 0 then
      let (n, sz) := p.psize iRoot
      let mut sz := sz + n
      let mut iRoot' := iRoot
      if p.eEdit == eDEL then
        if iLabel > 0 then
          sz := sz + (iRoot - iLabel)
          iRoot' := iLabel
        p := p.edit iRoot' sz none 0
      else if p.eEdit == eINS then pure ()
      else if p.eEdit == eAINS then
        if pi == 0 || bat path (pi - 1) != 93 then return (lNOTARRAY, p)
        p := p.edit iRoot' 0 (some p.ins) p.ins.size
      else
        p := p.edit iRoot' sz (some p.ins) p.ins.size
      return (iRoot', { p with iLabel := iLabel })
    return (iRoot, { p with iLabel := iLabel })
  let c := bat path pi
  if c == 46 then
    let x := bat p.b iRoot
    let pk := pi + 1
    let mut rawKey := true
    let mut zKey := pk
    let mut nKey := 0
    let mut i := 0
    if bat path pk == 34 then
      zKey := pk + 1
      i := 1
      while bat path (pk+i) != 0 && bat path (pk+i) != 34 do
        if bat path (pk+i) == 92 && bat path (pk+i+1) != 0 then i := i + 1
        i := i + 1
      nKey := i - 1
      if bat path (pk+i) != 0 then i := i + 1 else return (lPATHERROR, p)
      rawKey := !((sub path zKey nKey).data.contains 92)
    else
      zKey := pk
      i := 0
      while bat path (pk+i) != 0 && bat path (pk+i) != 46 && bat path (pk+i) != 91 do i := i + 1
      nKey := i
      if nKey == 0 then return (lPATHERROR, p)
    if x &&& 0x0f != tOBJECT then return (lNOTFOUND, p)
    let (n, sz) := p.psize iRoot
    let mut j := iRoot + n
    let iEnd := j + sz
    while j < iEnd do
      let x := p.typ j
      if x < tTEXT || x > tTEXTRAW then return (lERROR, p)
      let (n, sz) := p.psize j
      if n == 0 then return (lERROR, p)
      let k := j + n
      if k + sz ≥ iEnd then return (lERROR, p)
      let rawLabel := x == tTEXT || x == tTEXTRAW
      if labelEq path zKey nKey rawKey p.b k sz rawLabel then
        let v := k + sz
        if p.typ v > tOBJECT then return (lERROR, p)
        let (n, sz) := p.psize v
        if n == 0 || v + n + sz > iEnd then return (lERROR, p)
        p := { p with iDepth := u16inc p.iDepth }
        if p.iDepth ≥ maxDepth then return (lTOODEEP, p)
        let (rc, p') := lookupStep p v path (pk + i) j
        p := { p' with iDepth := u16dec p'.iDepth }
        p := p.adjustIf iRoot
        return (rc, p)
      j := k + sz
      if p.typ j > tOBJECT then return (lERROR, p)
      let (n, sz) := p.psize j
      if n == 0 then return (lERROR, p)
      j := j + n + sz
    if j > iEnd then return (lERROR, p)
    if p.eEdit ≥ eINS then
      if p.eEdit == eAINS && !endsWithBracket path (pk + i) then return (lNOTARRAY, p)
      let ix := header (if rawKey then tTEXTRAW else tTEXT5) nKey
      let (rc, v, p') := createSub p path (pk + i)
      p := p'
      if !isLookupErr rc then
        let nIns := ix.size + nKey + v.size
        p := p.edit j 0 none nIns
        p := { p with b := writeAt p.b j (ix ++ sub path zKey nKey ++ v) }
        p := p.adjustIf iRoot
      return (rc, p)
    return (lNOTFOUND, p)
  else if c == 91 then
    if p.typ iRoot != tARRAY then return (lNOTFOUND, p)
    let (n, sz) := p.psize iRoot
    let mut kk : Nat := 0
    let mut i := 1
    while isDigit (bat path (pi+i)) do
      if kk < 0xffffffff then kk := kk * 10 + (bat path (pi+i) - 48).toNat
      i := i + 1
    if i < 2 || bat path (pi+i) != 93 then
      if bat path (pi+1) == 35 then
        kk := p.arrayCount iRoot
        i := 2
        if bat path (pi+2) == 45 && isDigit (bat path (pi+3)) then
          let mut nn : Nat := 0
          i := 3
          repeat
            if nn < 0xffffffff then nn := nn * 10 + (bat path (pi+i) - 48).toNat
            i := i + 1
            if !isDigit (bat path (pi+i)) then break
          if nn > kk then return (lNOTFOUND, p)
          kk := kk - nn
        if bat path (pi+i) != 93 then return (lPATHERROR, p)
      else return (lPATHERROR, p)
    let mut j := iRoot + n
    let iEnd := j + sz
    while j < iEnd do
      if kk == 0 then
        p := { p with iDepth := u16inc p.iDepth }
        if p.iDepth ≥ maxDepth then return (lTOODEEP, p)
        let (rc, p') := lookupStep p j path (pi + i + 1) 0
        p := { p' with iDepth := u16dec p'.iDepth }
        p := p.adjustIf iRoot
        return (rc, p)
      kk := kk - 1
      let (n, sz) := p.psize j
      if n == 0 then return (lERROR, p)
      j := j + n + sz
    if j > iEnd then return (lERROR, p)
    if kk > 0 then return (lNOTFOUND, p)
    if p.eEdit ≥ eINS then
      let (rc, v, p') := createSub p path (pi + i + 1)
      p := p'
      if !isLookupErr rc then
        p := p.edit j 0 (some v) v.size
      p := p.adjustIf iRoot
      return (rc, p)
    return (lNOTFOUND, p)
  else return (lPATHERROR, p)

/-- `jsonCreateEditSubstructure`: the blob to insert for the rest of the path. -/
partial def createSub (p : JP) (path : ByteArray) (pi : Nat) : Nat × ByteArray × JP :=
  if bat path pi == 0 then (0, p.ins, p)
  else
    let root : UInt8 := if bat path pi == 46 then tOBJECT else tARRAY
    let q : JP := { b := ⟨#[root]⟩, eEdit := p.eEdit, ins := p.ins, iDepth := p.iDepth + 1 }
    if q.iDepth ≥ maxDepth then (lTOODEEP, .empty, p)
    else
      let (rc, q') := lookupStep q 0 path pi 0
      (rc, q'.b, { p with iDepth := u16dec p.iDepth })
end

/-! ## RFC 7396 merge patch (`jsonMergePatch`) -/

def mOK : Nat := 0
def mBADTARGET : Nat := 1
def mBADPATCH : Nat := 2
def mTOODEEP : Nat := 4

partial def mergePatch (t : JP) (iTarget : Nat) (pb : ByteArray) (iPatch : Nat) (depth : Nat) : Nat × JP := Id.run do
  let mut t := t
  let ps (i : Nat) := payloadSize pb 0 i
  let x := (bat pb iPatch) &&& 0x0f
  if x != tOBJECT then
    let (n, sz) := ps iPatch
    let szPatch := n + sz
    let (n, sz) := t.psize iTarget
    let szTarget := n + sz
    t := t.edit iTarget szTarget (some (sub pb iPatch szPatch)) szPatch
    return (mOK, t)
  if t.typ iTarget != tOBJECT then
    let (n, sz) := t.psize iTarget
    t := t.edit (iTarget + n) sz none 0
    let x := bat t.b iTarget
    t := { t with b := t.b.set! iTarget ((x &&& 0xf0) ||| tOBJECT) }
  let (n, sz) := ps iPatch
  if n == 0 then return (mBADPATCH, t)
  let mut iPCursor := iPatch + n
  let iPEnd := iPCursor + sz
  let (n, sz) := t.psize iTarget
  if n == 0 then return (mBADTARGET, t)
  let iTStart := iTarget + n
  let iTEndBE := iTStart + sz
  while iPCursor < iPEnd do
    let iPLabel := iPCursor
    let ePLabel := (bat pb iPCursor) &&& 0x0f
    if ePLabel < tTEXT || ePLabel > tTEXTRAW then return (mBADPATCH, t)
    let (nPLabel, szPLabel) := ps iPCursor
    if nPLabel == 0 then return (mBADPATCH, t)
    let iPValue := iPCursor + nPLabel + szPLabel
    if iPValue ≥ iPEnd then return (mBADPATCH, t)
    let (nPValue, szPValue) := ps iPValue
    if nPValue == 0 then return (mBADPATCH, t)
    iPCursor := iPValue + nPValue + szPValue
    if iPCursor > iPEnd then return (mBADPATCH, t)
    let mut iTCursor := iTStart
    let iTEnd : Nat := ((iTEndBE : Int) + t.delta).toNat
    let mut iTLabel := 0
    let mut nTLabel := 0
    let mut szTLabel := 0
    let mut nTValue := 0
    let mut szTValue := 0
    let mut iTValue := 0
    while iTCursor < iTEnd do
      iTLabel := iTCursor
      let eTLabel := t.typ iTCursor
      if eTLabel < tTEXT || eTLabel > tTEXTRAW then return (mBADTARGET, t)
      let (a, b) := t.psize iTCursor
      nTLabel := a; szTLabel := b
      if nTLabel == 0 then return (mBADTARGET, t)
      iTValue := iTLabel + nTLabel + szTLabel
      if iTValue ≥ iTEnd then return (mBADTARGET, t)
      let (a, b) := t.psize iTValue
      nTValue := a; szTValue := b
      if nTValue == 0 then return (mBADTARGET, t)
      if iTValue + nTValue + szTValue > iTEnd then return (mBADTARGET, t)
      let isEqual := labelEq pb (iPLabel + nPLabel) szPLabel (ePLabel == tTEXT || ePLabel == tTEXTRAW)
        t.b (iTLabel + nTLabel) szTLabel (eTLabel == tTEXT || eTLabel == tTEXTRAW)
      if isEqual then break
      iTCursor := iTValue + nTValue + szTValue
    let x := (bat pb iPValue) &&& 0x0f
    if iTCursor < iTEnd then
      if x == 0 then
        t := t.edit iTLabel (nTLabel + szTLabel + nTValue + szTValue) none 0
      else
        let savedDelta := t.delta
        t := { t with delta := 0 }
        if depth ≥ maxDepth then return (mTOODEEP, t)
        let (rc, t') := mergePatch t iTValue pb iPValue (depth + 1)
        t := t'
        if rc != 0 then return (rc, t)
        t := { t with delta := t.delta + savedDelta }
    else if x > 0 then
      let szNew := szPLabel + nPLabel
      if (bat pb iPValue) &&& 0x0f != tOBJECT then
        t := t.edit iTEnd 0 none (szPValue + nPValue + szNew)
        t := { t with b := writeAt t.b iTEnd (sub pb iPLabel szNew ++ sub pb iPValue (szPValue + nPValue)) }
      else
        t := t.edit iTEnd 0 none (szNew + 1)
        t := { t with b := writeAt t.b iTEnd (sub pb iPLabel szNew ++ ByteArray.mk #[0]) }
        let savedDelta := t.delta
        t := { t with delta := 0 }
        if depth ≥ maxDepth then return (mTOODEEP, t)
        let (rc, t') := mergePatch t (iTEnd + szNew) pb iPValue (depth + 1)
        t := t'
        if rc != 0 then return (rc, t)
        t := { t with delta := t.delta + savedDelta }
  t := t.adjustIf iTarget
  return (mOK, t)

end Sql.Json
