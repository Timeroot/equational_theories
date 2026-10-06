import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT.Actions

/-! Untrusted reconstruction of RUP hints from compact clause data.

This module proves nothing. Its output must be checked with `LRAT.check`;
`LRAT.check_sound` remains the sole connection to unsatisfiability. Keeping
this code in a precompiled library avoids interpreting the propagation loop.
-/
namespace Spectrum.CertificateData.CompactRup
open Std.Sat Std.Tactic.BVDecide.LRAT

private structure State where
  clauses : Array (Array Nat) := #[#[]]
  alive : ByteArray := ⟨#[0]⟩
  pinned : ByteArray := ⟨#[0]⟩
  -- Each long-clause watch carries a literal known to belong to the clause.
  -- A true blocker lets propagation skip loading/reordering that clause.
  watches : Array (Array (Nat × Nat))
  -- Binary clauses need only an implication edge, never watch relocation.
  binary : Array (Array (Nat × Nat))
  values : ByteArray
  reasons : Array Nat
  marks : Array Nat
  trail : Array Nat := #[]
  roots : Nat := 0
  units : Array Nat := #[]
  unitCursor : Nat := 0
  conflict : Nat := 0
  epoch : Nat := 0

private def emptyState : State := { watches := #[], binary := #[], values := ⟨#[]⟩, reasons := #[], marks := #[] }

@[inline] private def value (s : State) (a : Nat) : UInt8 :=
  let v := s.values[a/2]!
  if v == 0 then 0 else if v == (if a%2 == 0 then 1 else 2) then 1 else 2

@[inline] private def assign (s : State) (a r : Nat) : State :=
  { s with values := s.values.set! (a/2) (if a%2 == 0 then 1 else 2)
           reasons := s.reasons.set! (a/2) r
           trail := s.trail.push a }

private def restore (s : State) : State := Id.run do
  let mut s := s
  for k in [s.roots:s.trail.size] do
    s := { s with values := s.values.set! (s.trail[k]!/2) 0 }
  return { s with trail := s.trail.shrink s.roots }

private def insert (s : State) (input : Array Nat) : State := Id.run do
  let mut s := restore s
  let id := s.clauses.size
  let mut c := input.qsort (· < ·)
  let mut unique := #[]
  for a in c do
    if unique.isEmpty || unique.back! != a then unique := unique.push a
  c := unique
  let mut good := 0
  for k in [:c.size] do
    if value s c[k]! != 2 then
      c := c.swapIfInBounds good k
      good := good+1
  s := { s with clauses := s.clauses.push c, alive := s.alive.push 1,
                pinned := s.pinned.push 0 }
  if good == 0 then return { s with conflict := id }
  if good == 1 && value s c[0]! == 0 then
    s := { s with units := s.units.push id, pinned := s.pinned.set! id 1 }
  if c.size == 1 then
    s := { s with units := s.units.push id }
  else if c.size == 2 then
    s := { s with binary := s.binary.modify c[0]! (·.push (c[1]!,id)) }
    s := { s with binary := s.binary.modify c[1]! (·.push (c[0]!,id)) }
  else
    for k in [:2] do
      let a := c[k]!
      s := { s with watches := s.watches.modify a (·.push (id,c[1-k]!)) }
  return s

/-- Propagate a bounded trail; each variable is assigned at most once. -/
private def propagate (input : State) (start : Nat) : State × Nat := Id.run do
  let mut s := input
  let mut q := start
  for _ in [:s.values.size+1] do
    if q ≥ s.trail.size then break
    let falseLit := s.trail[q]! ^^^ 1
    q := q+1
    -- Do not rebuild watch lists for the many binary Latin constraints.
    for (a,id) in s.binary[falseLit]! do
      if s.alive[id]! == 0 then continue
      let v := value s a
      if v == 2 then return (s,id)
      if v == 0 then s := assign s a id
    let old := s.watches[falseLit]!
    s := { s with watches := s.watches.set! falseLit #[] }
    for z in [:old.size] do
      let (id,blocker) := old[z]!
      if s.alive[id]! == 0 then continue
      if value s blocker == 1 then
        s := { s with watches := s.watches.modify falseLit (·.push (id,blocker)) }
        continue
      let mut c := s.clauses[id]!
      if c[0]! == falseLit then c := c.swapIfInBounds 0 1
      if c.size < 2 || c[1]! != falseLit then return (s,0)
      if value s c[0]! == 1 then
        s := { s with clauses := s.clauses.set! id c,
                      watches := s.watches.modify falseLit (·.push (id,c[0]!)) }
        continue
      let mut replacement := c.size
      for j in [2:c.size] do
        if value s c[j]! != 2 then
          replacement := j
          break
      if replacement < c.size then
        c := c.swapIfInBounds 1 replacement
        s := { s with clauses := s.clauses.set! id c,
                      watches := s.watches.modify (c[1]!) (·.push (id,c[0]!)) }
      else
        s := { s with clauses := s.clauses.set! id c,
                      watches := s.watches.modify falseLit (·.push (id,c[0]!)) }
        if value s c[0]! == 2 then
          s := { s with watches := s.watches.modify falseLit (fun w => w ++ old.extract (z+1) old.size) }
          return (s,id)
        s := assign s c[0]! id
  return (s,0)

private def justify (input : State) (c : Array Nat) :
    Option (State × Array Nat × Bool) := Id.run do
  let mut s := restore input
  let mut conflict := s.conflict
  for _ in [:s.units.size] do
    if conflict != 0 || s.unitCursor ≥ s.units.size then break
    let id := s.units[s.unitCursor]!
    s := { s with unitCursor := s.unitCursor+1 }
    if s.alive[id]! == 0 then continue
    let a := s.clauses[id]![0]!
    if value s a == 2 then
      conflict := id
      break
    if value s a == 0 then s := assign s a id
  if conflict == 0 then
    let (next,r) := propagate s s.roots
    s := next
    conflict := r
  for k in [s.roots:s.trail.size] do
    let id := s.reasons[s.trail[k]!/2]!
    s := { s with pinned := s.pinned.set! id 1 }
  let already := conflict != 0
  s := { s with roots := s.trail.size, epoch := s.epoch+1,
                conflict := if already then conflict else s.conflict }
  let mut hints := #[]
  let mut trueLit := 0
  if !already then
    for a in c do
      if a < 2 || a/2 ≥ s.values.size then return none
      if value s a == 1 then
        trueLit := a
        break
  if trueLit != 0 then
    s := { s with marks := s.marks.set! (trueLit/2) s.epoch }
  else
    if !already then
      for a in c do
        if a < 2 || a/2 ≥ s.values.size then return none
        if value s a == 0 then s := assign s (a ^^^ 1) 0
      let (next,r) := propagate s s.roots
      s := next
      conflict := r
    if conflict == 0 then return none
    hints := hints.push conflict
    for a in s.clauses[conflict]! do
      s := { s with marks := s.marks.set! (a/2) s.epoch }
  for k in [:s.trail.size] do
    let a := s.trail[s.trail.size-1-k]!
    if s.marks[a/2]! != s.epoch then continue
    let r := s.reasons[a/2]!
    if r == 0 then continue
    hints := hints.push r
    for b in s.clauses[r]! do
      if b != a then s := { s with marks := s.marks.set! (b/2) s.epoch }
  return some (s,hints.reverse,already)

@[inline] private def readNat (bytes : ByteArray) (pos : Nat) : Nat × Nat := Id.run do
  let mut result := 0
  let mut pos := pos
  for k in [:10] do
    let b := bytes[pos]!.toNat
    pos := pos+1
    result := result ||| ((b%128) <<< (7*k))
    if b < 128 then break
  return (result,pos)

private def toLiteral (a : Nat) : Int :=
  if a%2 == 0 then Int.ofNat (a/2) else -Int.ofNat (a/2)

/-- Recover a conventional LRAT proof. A corrupt stream or failed replay does
not establish anything: the caller must still use the verified LRAT checker. -/
def reconstruct (bytes : ByteArray) (cnf : CNF Nat) : Array IntAction := Id.run do
  let (initial,header) := readNat bytes 0
  if initial/2 != cnf.clauses.size+1 then return #[]
  -- An optional mask identifies the input clauses used by the captured proof.
  -- This only prunes the untrusted hint search. Clause IDs are preserved, and
  -- the verified checker still checks against the entire original CNF.
  let masked := bytes[header]! == 109 -- 'm'; old streams begin with 'a'.
  let pos₀ := if masked then header+1+initial/2 else header
  if pos₀ > bytes.size then return #[]
  let mut bound := 1
  for c in cnf.clauses do
    for l in c do bound := max bound (l.1+2)
  let mut s : State := {
    watches := Array.replicate (2*bound+2) #[]
    binary := Array.replicate (2*bound+2) #[]
    values := ⟨Array.replicate bound 0⟩
    reasons := Array.replicate bound 0
    marks := Array.replicate bound 0 }
  for c in cnf.clauses do
    if masked && bytes[header+1+s.clauses.size]! == 0 then
      s := { s with clauses := s.clauses.push #[], alive := s.alive.push 0,
                    pinned := s.pinned.push 0 }
    else
      s := insert s (c.toArray.map fun (v,b) => 2*(v+1) + if b then 0 else 1)
  let mut pos := pos₀
  let mut history : Array (Array Nat) := Array.replicate 256 #[]
  let mut count := 0
  let mut proof := #[]
  for _ in [:bytes.size] do
    if pos ≥ bytes.size then break
    let tag := bytes[pos]!.toNat
    pos := pos+1
    if tag == 97 then
      let (back,next) := readNat bytes pos
      pos := next
      let mut c := #[]
      if back != 0 then
        if back > count || back > 256 then return #[]
        let prev := history[(count-back)%256]!
        let (mask,next) := readNat bytes pos
        pos := next
        for k in [:prev.size] do
          if (mask >>> k) &&& 1 == 1 then c := c.push prev[k]!
      let mut previous := 0
      for _ in [:bytes.size-pos] do
        let (v,next) := readNat bytes pos
        pos := next
        if v == 0 then break
        previous := previous+v-1
        c := c.push previous
      c := c.qsort (· < ·)
      history := history.set! (count%256) c
      count := count+1
      -- Release the old state before the fallible call. Keeping it live across
      -- this match forces a copy of the whole clause database on every step.
      let current := s
      s := emptyState
      let some (next,hints,already) := justify current c | return #[]
      s := next
      let id := s.clauses.size
      if already || c.isEmpty then
        return proof.push (.addEmpty id hints)
      proof := proof.push (.addRup id (c.map toLiteral) hints)
      s := insert s c
    else if tag == 100 then
      let mut previous := 0
      let mut ids := #[]
      for _ in [:bytes.size-pos] do
        let (v,next) := readNat bytes pos
        pos := next
        if v == 0 then break
        previous := previous+v-1
        if s.pinned[previous]! == 0 then
          s := { s with alive := s.alive.set! previous 0 }
          ids := ids.push previous
      if !ids.isEmpty then proof := proof.push (.del ids)
    else return #[]
  return proof

end Spectrum.CertificateData.CompactRup
