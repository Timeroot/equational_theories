import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Perm.Basic

/-! The twenty-one sorted tails of an idempotent rank-four row fall into five
orbits under renaming its three nonzero image points. The permutations rename
the corresponding column-image points and sort the five remaining labels. -/
namespace Spectrum.E1483.OrderTwelve.RowsData
abbrev A := Fin 12
abbrev Row := A → A
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def rowData : Array (Array Nat) := #[
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 1, 1, 1],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 1, 1, 2],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 1, 1, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 1, 2, 2],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 1, 2, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 1, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 2, 2, 2],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 2, 2, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 2, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 1, 3, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 2, 2, 2, 2],
  #[0, 0, 0, 0, 1, 2, 3, 1, 2, 2, 2, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 2, 2, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 2, 3, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 1, 3, 3, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 2, 2, 2, 2, 2],
  #[0, 0, 0, 0, 1, 2, 3, 2, 2, 2, 2, 3],
  #[0, 0, 0, 0, 1, 2, 3, 2, 2, 2, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 2, 2, 3, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 2, 3, 3, 3, 3],
  #[0, 0, 0, 0, 1, 2, 3, 3, 3, 3, 3, 3]]

private def permutationData : Array (Array Nat) := #[
  #[0, 3, 1, 2, 6, 4, 5, 7, 8, 9, 10, 11],
  #[0, 3, 2, 1, 6, 5, 4, 8, 9, 10, 11, 7],
  #[0, 3, 1, 2, 6, 4, 5, 8, 9, 10, 11, 7],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 3, 1, 2, 6, 4, 5, 9, 10, 11, 7, 8],
  #[0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 10, 11],
  #[0, 2, 1, 3, 5, 4, 6, 10, 11, 7, 8, 9],
  #[0, 2, 3, 1, 5, 6, 4, 8, 9, 10, 11, 7],
  #[0, 2, 1, 3, 5, 4, 6, 8, 9, 7, 10, 11],
  #[0, 2, 3, 1, 5, 6, 4, 10, 11, 7, 8, 9],
  #[0, 2, 3, 1, 5, 6, 4, 7, 8, 9, 10, 11],
  #[0, 1, 3, 2, 4, 6, 5, 7, 9, 10, 11, 8],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 2, 1, 3, 5, 4, 6, 7, 8, 9, 10, 11],
  #[0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 10, 11],
  #[0, 1, 3, 2, 4, 6, 5, 8, 9, 10, 11, 7],
  #[0, 3, 1, 2, 6, 4, 5, 7, 8, 9, 10, 11],
  #[0, 3, 2, 1, 6, 5, 4, 10, 11, 7, 8, 9],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]

private def inverseData : Array (Array Nat) := #[
  #[0, 2, 3, 1, 5, 6, 4, 7, 8, 9, 10, 11],
  #[0, 3, 2, 1, 6, 5, 4, 11, 7, 8, 9, 10],
  #[0, 2, 3, 1, 5, 6, 4, 11, 7, 8, 9, 10],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 2, 3, 1, 5, 6, 4, 10, 11, 7, 8, 9],
  #[0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 10, 11],
  #[0, 2, 1, 3, 5, 4, 6, 9, 10, 11, 7, 8],
  #[0, 3, 1, 2, 6, 4, 5, 11, 7, 8, 9, 10],
  #[0, 2, 1, 3, 5, 4, 6, 9, 7, 8, 10, 11],
  #[0, 3, 1, 2, 6, 4, 5, 9, 10, 11, 7, 8],
  #[0, 3, 1, 2, 6, 4, 5, 7, 8, 9, 10, 11],
  #[0, 1, 3, 2, 4, 6, 5, 7, 11, 8, 9, 10],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 2, 1, 3, 5, 4, 6, 7, 8, 9, 10, 11],
  #[0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 10, 11],
  #[0, 1, 3, 2, 4, 6, 5, 11, 7, 8, 9, 10],
  #[0, 2, 3, 1, 5, 6, 4, 7, 8, 9, 10, 11],
  #[0, 3, 2, 1, 6, 5, 4, 9, 10, 11, 7, 8],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]

def row (i : Fin 21) (x : A) : A :=
  ⟨rowData[i.val]![x.val]! % 12, Nat.mod_lt _ (by decide)⟩

def forward (i : Fin 21) (x : A) : A :=
  ⟨permutationData[i.val]![x.val]! % 12, Nat.mod_lt _ (by decide)⟩

def backward (i : Fin 21) (x : A) : A :=
  ⟨inverseData[i.val]![x.val]! % 12, Nat.mod_lt _ (by decide)⟩

private theorem inverses : ∀ (i : Fin 21) (x : A),
    backward i (forward i x) = x ∧ forward i (backward i x) = x := by decide

def permutation (i : Fin 21) : Equiv.Perm A where
  toFun := forward i
  invFun := backward i
  left_inv x := (inverses i x).1
  right_inv x := (inverses i x).2

def representative (i : Fin 5) : Fin 21 :=
  ⟨#[20, 19, 3, 13, 12][i.val]! % 21, Nat.mod_lt _ (by decide)⟩

def target (i : Fin 21) : Fin 5 :=
  ⟨#[0, 1, 1, 2, 3, 2, 2, 4, 4, 2, 1, 3, 4, 3, 1, 0, 1, 2, 2, 1, 0][i.val]! % 5, Nat.mod_lt _ (by decide)⟩

def column : Finset A := {0,4,5,6}

lemma zero_fixed : ∀ i : Fin 21, permutation i 0 = 0 := by decide
lemma column_preserved : ∀ (i : Fin 21) (x : A),
    permutation i x ∈ column ↔ x ∈ column := by decide
lemma conjugates : ∀ (i : Fin 21) (x : A),
    permutation i (row i ((permutation i).symm x)) = row (representative (target i)) x :=
  by decide

lemma row_image : ∀ (i : Fin 21) (z : A), (∃ x, row i x = z) ↔ z.val < 4 := by decide
lemma head_zero : ∀ (i : Fin 21) (x : A), x.val ≤ 3 → row i x = 0 := by decide
lemma first_occurrence : ∀ (i : Fin 21) (a d : A),
    a ∈ ([4,5,6] : List A) → row i d = row i a → a ≤ d := by decide
lemma key_sorted : ∀ (r : Fin 21) (i j : A), 3 < i.val → 3 < j.val → i ≤ j →
    (if i ∈ column then (row r i).val else 12 + (row r i).val) ≤
    (if j ∈ column then (row r j).val else 12 + (row r j).val) := by decide

end Spectrum.E1483.OrderTwelve.RowsData
