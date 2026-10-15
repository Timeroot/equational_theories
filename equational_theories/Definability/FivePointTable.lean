import equational_theories.Definability.FourPointTable

/-! Five-element tables use 25 three-bit entries. The bit-level decoder is only
used on the five legitimate point values; the validity check excludes unused
bit patterns before a finite coverage certificate is applied. -/
namespace Magma.FivePointTable
abbrev Point := Fin 5
abbrev Code := BitVec 75

def point (x : Point) : BitVec 3 := BitVec.ofNat 3 x.val

def bits (c : Code) (x y : BitVec 3) : BitVec 3 :=
  if x = 0 then (if y = 0 then c.extractLsb' 0 3 else if y = 1 then c.extractLsb' 3 3 else if y = 2 then c.extractLsb' 6 3 else if y = 3 then c.extractLsb' 9 3 else c.extractLsb' 12 3) else
  if x = 1 then (if y = 0 then c.extractLsb' 15 3 else if y = 1 then c.extractLsb' 18 3 else if y = 2 then c.extractLsb' 21 3 else if y = 3 then c.extractLsb' 24 3 else c.extractLsb' 27 3) else
  if x = 2 then (if y = 0 then c.extractLsb' 30 3 else if y = 1 then c.extractLsb' 33 3 else if y = 2 then c.extractLsb' 36 3 else if y = 3 then c.extractLsb' 39 3 else c.extractLsb' 42 3) else
  if x = 3 then (if y = 0 then c.extractLsb' 45 3 else if y = 1 then c.extractLsb' 48 3 else if y = 2 then c.extractLsb' 51 3 else if y = 3 then c.extractLsb' 54 3 else c.extractLsb' 57 3) else
  (if y = 0 then c.extractLsb' 60 3 else if y = 1 then c.extractLsb' 63 3 else if y = 2 then c.extractLsb' 66 3 else if y = 3 then c.extractLsb' 69 3 else c.extractLsb' 72 3)

def decode (c : Code) (x y : Point) : Point := Fin.ofNat 5 (bits c (point x) (point y)).toNat

def encode (f : Point → Point → Point) : Code :=
  point (f 4 4) ++ point (f 4 3) ++ point (f 4 2) ++ point (f 4 1) ++ point (f 4 0) ++ point (f 3 4) ++ point (f 3 3) ++ point (f 3 2) ++ point (f 3 1) ++ point (f 3 0) ++ point (f 2 4) ++ point (f 2 3) ++ point (f 2 2) ++ point (f 2 1) ++ point (f 2 0) ++ point (f 1 4) ++ point (f 1 3) ++ point (f 1 2) ++ point (f 1 1) ++ point (f 1 0) ++ point (f 0 4) ++ point (f 0 3) ++ point (f 0 2) ++ point (f 0 1) ++ point (f 0 0)

theorem bits_encode (f : Point → Point → Point) (x y : Point) :
    bits (encode f) (point x) (point y) = point (f x y) := by
  fin_cases x <;> fin_cases y <;>
    simp [bits, encode, point] <;>
    (repeat' first
      | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
      | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]) <;>
    exact BitVec.extractLsb'_eq_self

theorem point_back (x : Point) : Fin.ofNat 5 (point x).toNat = x := by
  fin_cases x <;> rfl

theorem point_lt (x : Point) : point x < (5 : BitVec 3) := by
  fin_cases x <;> decide

theorem decode_encode (f : Point → Point → Point) : decode (encode f) = f := by
  funext x y
  exact (congrArg (fun z : BitVec 3 => Fin.ofNat 5 z.toNat) (bits_encode f x y)).trans
    (point_back (f x y))

def Valid (c : Code) : Prop :=
  bits c 0 0 < 5 ∧
  bits c 0 1 < 5 ∧
  bits c 0 2 < 5 ∧
  bits c 0 3 < 5 ∧
  bits c 0 4 < 5 ∧
  bits c 1 0 < 5 ∧
  bits c 1 1 < 5 ∧
  bits c 1 2 < 5 ∧
  bits c 1 3 < 5 ∧
  bits c 1 4 < 5 ∧
  bits c 2 0 < 5 ∧
  bits c 2 1 < 5 ∧
  bits c 2 2 < 5 ∧
  bits c 2 3 < 5 ∧
  bits c 2 4 < 5 ∧
  bits c 3 0 < 5 ∧
  bits c 3 1 < 5 ∧
  bits c 3 2 < 5 ∧
  bits c 3 3 < 5 ∧
  bits c 3 4 < 5 ∧
  bits c 4 0 < 5 ∧
  bits c 4 1 < 5 ∧
  bits c 4 2 < 5 ∧
  bits c 4 3 < 5 ∧
  bits c 4 4 < 5

theorem valid_encode (f : Point → Point → Point) : Valid (encode f) := by
  have h (x y : Point) : bits (encode f) (point x) (point y) < 5 := by
    rw [bits_encode]
    exact point_lt _
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 0 4, h 1 0, h 1 1, h 1 2, h 1 3, h 1 4, h 2 0, h 2 1, h 2 2, h 2 3, h 2 4, h 3 0, h 3 1, h 3 2, h 3 3, h 3 4, h 4 0, h 4 1, h 4 2, h 4 3, h 4 4⟩

end Magma.FivePointTable

/-- info: 'Magma.FivePointTable.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FivePointTable.decode_encode
