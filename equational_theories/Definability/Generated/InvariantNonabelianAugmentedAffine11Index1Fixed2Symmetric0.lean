import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianAugmentedAffine11Index1Fixed2Symmetric0

def genData : Array (Array (Fin 13)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11, 12], #[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 12], #[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12], #[0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11, 12]]
def gen (i : Fin 4) (x : Fin 13) : Fin 13 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 13)) := #[#[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12], #[0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11, 12], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11, 12], #[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 12]]
def genInv (i : Fin 4) (x : Fin 13) : Fin 13 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 13)) := #[]
def probe (i : Fin 0) (x : Fin 13) : Fin 13 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 13)) := #[]
def probeInv (i : Fin 0) (x : Fin 13) : Fin 13 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 13)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]]
def sourceRow (i : Fin 13) (x : Fin 13) : Fin 13 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 13) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 13) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [3, 0], [1, 2], [3, 2], [0, 0, 0], [1, 0, 0], [0, 3, 0], [2, 1, 2], [0, 1, 1, 2, 1, 2], [1], [3], [1, 0], [0, 1], [1, 1], [2, 1], [2, 2], [0, 3], [2, 3], [3, 3], [0, 1, 0], [1, 1, 0], [3, 3, 0], [1, 0, 1], [3, 0, 1], [0, 1, 1], [2, 1, 1], [1, 2, 1], [3, 2, 1], [1, 1, 2], [1, 2, 2], [2, 2, 2], [2, 3, 2], [3, 3, 2], [0, 0, 3], [3, 0, 3], [2, 2, 3], [3, 2, 3], [0, 3, 3], [2, 3, 3], [3, 3, 3], [0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [1, 0, 1, 0], [3, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [2, 1, 1, 0], [0, 0, 3, 0], [3, 0, 3, 0], [0, 3, 3, 0], [2, 3, 3, 0], [3, 3, 3, 0], [1, 1, 0, 1], [3, 3, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [2, 1, 1, 1], [1, 2, 1, 1], [1, 1, 2, 1], [1, 1, 1, 2], [2, 3, 3, 2], [3, 3, 3, 2], [3, 3, 0, 3], [3, 3, 2, 3], [3, 0, 3, 3], [3, 2, 3, 3], [0, 3, 3, 3], [2, 3, 3, 3], [3, 3, 3, 3], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 2, 1, 1, 0], [3, 0, 3, 3, 0], [3, 3, 3, 3, 0], [1, 1, 1, 0, 1], [1, 1, 0, 1, 1], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1], [1, 1, 1, 1, 1], [2, 1, 1, 1, 1], [1, 2, 1, 1, 1], [1, 1, 2, 1, 1], [1, 1, 1, 2, 1], [1, 1, 1, 1, 2], [3, 2, 3, 3, 2], [3, 3, 3, 3, 2], [3, 3, 3, 0, 3], [3, 3, 3, 2, 3], [3, 3, 0, 3, 3], [3, 3, 2, 3, 3], [3, 0, 3, 3, 3], [3, 2, 3, 3, 3], [0, 3, 3, 3, 3], [2, 3, 3, 3, 3], [1, 1, 1, 1, 1, 0], [1, 1, 1, 1, 0, 1], [1, 1, 1, 0, 1, 1], [1, 1, 0, 1, 1, 1], [1, 0, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1], [1, 2, 1, 1, 1, 1], [1, 1, 2, 1, 1, 1], [1, 1, 1, 2, 1, 1], [1, 1, 1, 1, 2, 1]]
def words (i : Fin 110) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 13 × Fin 13) := #[(0, 0), (0, 1), (0, 11), (0, 12), (11, 0), (11, 11), (11, 12), (12, 0), (12, 11), (12, 12)]
def rep (i : Fin 10) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 10 × Fin 110)) := #[#[(0, 0), (1, 0), (1, 12), (1, 21), (1, 16), (1, 61), (1, 13), (1, 42), (1, 11), (1, 74), (1, 84), (2, 0), (3, 0)], #[(1, 105), (0, 1), (1, 1), (1, 15), (1, 40), (1, 27), (1, 83), (1, 19), (1, 72), (1, 60), (1, 98), (2, 1), (3, 1)], #[(1, 91), (1, 104), (0, 3), (1, 3), (1, 14), (1, 55), (1, 25), (1, 82), (1, 36), (1, 78), (1, 59), (2, 3), (3, 3)], #[(1, 65), (1, 94), (1, 108), (0, 7), (1, 7), (1, 22), (1, 24), (1, 51), (1, 88), (1, 58), (1, 68), (2, 7), (3, 7)], #[(1, 67), (1, 57), (1, 93), (1, 103), (0, 8), (1, 43), (1, 8), (1, 54), (1, 23), (1, 81), (1, 34), (2, 8), (3, 8)], #[(1, 6), (1, 71), (1, 75), (1, 97), (1, 101), (0, 6), (1, 30), (1, 45), (1, 39), (1, 49), (1, 76), (2, 6), (3, 6)], #[(1, 89), (1, 4), (1, 70), (1, 77), (1, 96), (1, 109), (0, 4), (1, 26), (1, 44), (1, 37), (1, 47), (2, 4), (3, 4)], #[(1, 31), (1, 87), (1, 9), (1, 56), (1, 64), (1, 92), (1, 107), (0, 9), (1, 48), (1, 32), (1, 66), (2, 9), (3, 9)], #[(1, 35), (1, 46), (1, 80), (1, 52), (1, 69), (1, 50), (1, 95), (1, 102), (0, 10), (1, 33), (1, 10), (2, 10), (3, 10)], #[(1, 5), (1, 53), (1, 29), (1, 86), (1, 38), (1, 90), (1, 63), (1, 79), (1, 106), (0, 5), (1, 18), (2, 5), (3, 5)], #[(1, 2), (1, 17), (1, 41), (1, 28), (1, 85), (1, 20), (1, 73), (1, 62), (1, 99), (1, 100), (0, 2), (2, 2), (3, 2)], #[(4, 0), (4, 1), (4, 3), (4, 7), (4, 8), (4, 6), (4, 4), (4, 9), (4, 10), (4, 5), (4, 2), (5, 0), (6, 0)], #[(7, 0), (7, 1), (7, 3), (7, 7), (7, 8), (7, 6), (7, 4), (7, 9), (7, 10), (7, 5), (7, 2), (8, 0), (9, 0)]]
def tr (x y : Fin 13) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 10 → ℕ := ![3, 13, 3, 3, 3, 2, 2, 3, 2, 2]
def valuesData : Array (Array (Fin 13)) := #[#[0, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 11, 12], #[0, 11, 12], #[0, 11, 12], #[11, 12], #[11, 12], #[0, 11, 12], #[11, 12], #[11, 12]]
def values (i : Fin 10) (j : Fin (sizes i)) : Fin 13 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 110)) := #[#[11], #[0], #[11], #[11], #[11], #[1], #[1], #[11], #[1], #[1]]
def stabilizers (i : Fin 10) (j : Fin 1) : Fin 110 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 10) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 13) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 13) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 13)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem same_orbit : ∀ i x y, (tr (genPerm i x) (genPerm i y)).1 = (tr x y).1 := by native_decide
theorem coherent_values : ∀ i x y a,
    genPerm i (wordPerm genPerm (words (tr x y).2) (values (tr x y).1 a)) =
    wordPerm genPerm (words (tr (genPerm i x) (genPerm i y)).2) (values (tr x y).1 a) := by native_decide

theorem family_generators : ∀ p i, (fam p).IsEndo (genPerm i) :=
  Magma.InvariantFamily.family_endos genPerm words tr sizes values same_orbit coherent_values

theorem tr_rep : ∀ i, tr (rep i).1 (rep i).2 = (i, 0) := by native_decide
theorem words_zero : words 0 = [] := by native_decide
theorem values_injective : ∀ i, Function.Injective (values i) := by native_decide

theorem op_rep (p : Params) (i) : (fam p).op (rep i).1 (rep i).2 = values i (p i) := by
  change wordPerm genPerm (words (tr (rep i).1 (rep i).2).2)
    (values (tr (rep i).1 (rep i).2).1 (p (tr (rep i).1 (rep i).2).1)) = _
  rw [tr_rep]
  change wordPerm genPerm (words 0) (values i (p i)) = _
  rw [words_zero]
  rfl

theorem family_injective : Function.Injective (fun p : Params => (fam p).op) := by
  intro p q hpq
  funext i
  apply values_injective i
  rw [← op_rep p i, ← op_rep q i]
  exact congrFun (congrFun hpq (rep i).1) (rep i).2

def points : Fin 3 → Fin 13 := ![0, 11, 12]
def point_index : Fin 13 → Fin 3 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

private def law100 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Leaf 1)))⟩
private theorem count100 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law100} = 564 := by native_decide

private def law1250 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)) (.Leaf 2)))⟩
private theorem count1250 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1250} = 569 := by native_decide

end Magma.InvariantNonabelianAugmentedAffine11Index1Fixed2Symmetric0

open Magma.InvariantNonabelianAugmentedAffine11Index1Fixed2Symmetric0 Magma.InvariantFamily

theorem Equation100_not_termStructuralFromFin_Equation1250_invariantFamilyCount : ¬ Law100.TermStructuralFromFin Law1250 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1250) (fun p => OrbitTest points (fam p) law100)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1250, count100]
    decide

/-- info: 'Equation100_not_termStructuralFromFin_Equation1250_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_cover._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count100._native.native_decide.ax_1_1,
 count1250._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation100_not_termStructuralFromFin_Equation1250_invariantFamilyCount

