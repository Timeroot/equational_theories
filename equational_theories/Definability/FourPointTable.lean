import equational_theories.Definability.FiniteEndomorphismCover
import Std.Tactic.BVDecide
import Mathlib.Data.BitVec

/-! A four-element table packed into 32 bits. The encoding lemmas are purely
mathematical; particular finite coverage certificates can use this representation. -/
namespace Magma.FourPointTable

abbrev Point := BitVec 2
abbrev Code := BitVec 32

instance : Fintype Point :=
  Fintype.ofEquiv (Fin 4) (BitVec.equivFin (m := 2)).symm.toEquiv

def decode (c : Code) (x y : Point) : Point :=
  if x = 0 then (if y = 0 then c.extractLsb' 0 2 else if y = 1 then c.extractLsb' 2 2 else if y = 2 then c.extractLsb' 4 2 else c.extractLsb' 6 2) else
  if x = 1 then (if y = 0 then c.extractLsb' 8 2 else if y = 1 then c.extractLsb' 10 2 else if y = 2 then c.extractLsb' 12 2 else c.extractLsb' 14 2) else
  if x = 2 then (if y = 0 then c.extractLsb' 16 2 else if y = 1 then c.extractLsb' 18 2 else if y = 2 then c.extractLsb' 20 2 else c.extractLsb' 22 2) else
  (if y = 0 then c.extractLsb' 24 2 else if y = 1 then c.extractLsb' 26 2 else if y = 2 then c.extractLsb' 28 2 else c.extractLsb' 30 2)

def encode (f : Point → Point → Point) : Code :=
  f 3 3 ++ f 3 2 ++ f 3 1 ++ f 3 0 ++ f 2 3 ++ f 2 2 ++ f 2 1 ++ f 2 0 ++ f 1 3 ++ f 1 2 ++ f 1 1 ++ f 1 0 ++ f 0 3 ++ f 0 2 ++ f 0 1 ++ f 0 0

theorem point_cases : ∀ x : Point, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  decide +kernel

theorem decode_encode (f : Point → Point → Point) : decode (encode f) = f := by
  funext x y
  rcases point_cases x with rfl | rfl | rfl | rfl <;>
    rcases point_cases y with rfl | rfl | rfl | rfl <;>
    simp [decode, encode] <;>
    (repeat' first
      | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
      | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]) <;>
    exact BitVec.extractLsb'_eq_self

theorem encode_decode (c : Code) : encode (decode c) = c := by
  change c.extractLsb' 30 2 ++ c.extractLsb' 28 2 ++ c.extractLsb' 26 2 ++ c.extractLsb' 24 2 ++ c.extractLsb' 22 2 ++ c.extractLsb' 20 2 ++ c.extractLsb' 18 2 ++ c.extractLsb' 16 2 ++ c.extractLsb' 14 2 ++ c.extractLsb' 12 2 ++ c.extractLsb' 10 2 ++ c.extractLsb' 8 2 ++ c.extractLsb' 6 2 ++ c.extractLsb' 4 2 ++ c.extractLsb' 2 2 ++ c.extractLsb' 0 2 = c
  repeat' rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem decode_injective : Function.Injective decode := by
  intro a b h
  rw [← encode_decode a, ← encode_decode b, h]

end Magma.FourPointTable

/-- info: 'Magma.FourPointTable.decode_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FourPointTable.decode_encode
/-- info: 'Magma.FourPointTable.encode_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FourPointTable.encode_decode
