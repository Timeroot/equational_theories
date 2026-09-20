import equational_theories.Definability.TransitiveInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantRing2Degree3TruncatedPower2

def genData : Array (Array (Fin 8)) := #[#[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[4, 5, 6, 7, 0, 1, 2, 3], #[0, 5, 2, 7, 4, 1, 6, 3]]
def gen (i : Fin 4) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[4, 5, 6, 7, 0, 1, 2, 3], #[0, 5, 2, 7, 4, 1, 6, 3]]
def genInv (i : Fin 4) (x : Fin 8) : Fin 8 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 8)) := #[]
def probe (i : Fin 0) (x : Fin 8) : Fin 8 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 8)) := #[]
def probeInv (i : Fin 0) (x : Fin 8) : Fin 8 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 8)) := #[#[0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7]]
def sourceRow (i : Fin 8) (x : Fin 8) : Fin 8 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 8) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 8) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [1], [2], [1, 0], [2, 0], [2, 1], [2, 1, 0], [0, 1, 3, 2, 1, 0], [3, 0], [3, 1], [3, 2], [0, 3], [3, 1, 0], [3, 2, 1], [0, 3, 1]]
def words (i : Fin 16) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 6)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 16)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (1, 8), (5, 0), (3, 8)], #[(1, 1), (0, 1), (3, 1), (2, 1), (1, 12), (4, 1), (3, 12), (5, 1)], #[(2, 2), (3, 2), (0, 2), (1, 2), (5, 2), (3, 10), (4, 2), (1, 10)], #[(3, 4), (2, 4), (1, 4), (0, 4), (3, 15), (5, 4), (1, 15), (4, 4)], #[(4, 3), (1, 11), (5, 3), (3, 11), (0, 3), (1, 3), (2, 3), (3, 3)], #[(1, 9), (4, 5), (3, 9), (5, 5), (1, 5), (0, 5), (3, 5), (2, 5)], #[(5, 6), (3, 14), (4, 6), (1, 14), (2, 6), (3, 6), (0, 6), (1, 6)], #[(3, 13), (5, 7), (1, 13), (4, 7), (3, 7), (2, 7), (1, 7), (0, 7)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![4, 8, 4, 8, 4, 4]
def valuesData : Array (Array (Fin 8)) := #[#[0, 2, 4, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 4, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 4, 6], #[0, 2, 4, 6]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 16)) := #[#[8], #[0], #[8], #[0], #[8], #[8]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 16 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 6) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 8) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 8) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 8)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
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

theorem point_transitive : ∀ a,
    wordPerm genPerm (words (tr a a).2) 0 = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

private def law1461 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 2) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count1461 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 8) (fam p) law1461} = 33 := by native_decide

private def law1469 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 2) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count1469 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 8) (fam p) law1469} = 37 := by native_decide

private def law1650 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Fork (.Leaf 0) (.Leaf 2)) (.Leaf 0)))⟩
private theorem count1650 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 8) (fam p) law1650} = 868 := by native_decide

private def law3515 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 2)) (.Leaf 1)))⟩
private theorem count3515 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 8) (fam p) law3515} = 33 := by native_decide

private def law4269 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0)))⟩
private theorem count4269 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 8) (fam p) law4269} = 860 := by native_decide

end Magma.InvariantRing2Degree3TruncatedPower2

open Magma.InvariantRing2Degree3TruncatedPower2 Magma.InvariantFamily

theorem Equation1461_not_termStructuralFromFin_Equation1469_invariantFamilyCount : ¬ Law1461.TermStructuralFromFin Law1469 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 8) (fam p) law1469) (fun p => PointTest (0 : Fin 8) (fam p) law1461)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1469, count1461]
    decide

/-- info: 'Equation1461_not_termStructuralFromFin_Equation1469_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1461._native.native_decide.ax_1_1,
 count1469._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1461_not_termStructuralFromFin_Equation1469_invariantFamilyCount

theorem Equation3515_not_termStructuralFromFin_Equation1469_invariantFamilyCount : ¬ Law3515.TermStructuralFromFin Law1469 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 8) (fam p) law1469) (fun p => PointTest (0 : Fin 8) (fam p) law3515)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1469, count3515]
    decide

/-- info: 'Equation3515_not_termStructuralFromFin_Equation1469_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1469._native.native_decide.ax_1_1,
 count3515._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3515_not_termStructuralFromFin_Equation1469_invariantFamilyCount

theorem Equation4269_not_termStructuralFromFin_Equation1650_invariantFamilyCount : ¬ Law4269.TermStructuralFromFin Law1650 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 8) (fam p) law1650) (fun p => PointTest (0 : Fin 8) (fam p) law4269)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1650, count4269]
    decide

/-- info: 'Equation4269_not_termStructuralFromFin_Equation1650_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1650._native.native_decide.ax_1_1,
 count4269._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4269_not_termStructuralFromFin_Equation1650_invariantFamilyCount

