import equational_theories.Definability.InvariantFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianAugmentedAffine7Index2Fixed1Symmetric0

def genData : Array (Array (Fin 8)) := #[#[1, 2, 3, 4, 5, 6, 0, 7], #[0, 2, 4, 6, 1, 3, 5, 7], #[6, 0, 1, 2, 3, 4, 5, 7], #[0, 4, 1, 5, 2, 6, 3, 7]]
def gen (i : Fin 4) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[6, 0, 1, 2, 3, 4, 5, 7], #[0, 4, 1, 5, 2, 6, 3, 7], #[1, 2, 3, 4, 5, 6, 0, 7], #[0, 2, 4, 6, 1, 3, 5, 7]]
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

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [3, 0], [1, 2], [3, 2], [0, 0, 1, 2], [3], [1, 0], [0, 1], [2, 1], [2, 2], [0, 3], [2, 3], [0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 3, 0], [1, 0, 1], [3, 0, 1]]
def words (i : Fin 21) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 3), (0, 7), (7, 0), (7, 7)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 21)) := #[#[(0, 0), (1, 0), (1, 7), (2, 0), (1, 8), (2, 8), (2, 7), (3, 0)], #[(2, 10), (0, 1), (1, 1), (1, 10), (2, 1), (1, 13), (2, 13), (3, 1)], #[(2, 19), (2, 9), (0, 3), (1, 3), (1, 9), (2, 3), (1, 19), (3, 3)], #[(1, 6), (2, 6), (2, 17), (0, 6), (1, 15), (1, 17), (2, 15), (3, 6)], #[(2, 20), (1, 4), (2, 4), (2, 16), (0, 4), (1, 20), (1, 16), (3, 4)], #[(1, 5), (2, 12), (1, 18), (2, 18), (2, 5), (0, 5), (1, 12), (3, 5)], #[(1, 2), (1, 11), (2, 2), (1, 14), (2, 14), (2, 11), (0, 2), (3, 2)], #[(4, 0), (4, 1), (4, 3), (4, 6), (4, 4), (4, 5), (4, 2), (5, 0)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![2, 8, 8, 2, 2, 1]
def valuesData : Array (Array (Fin 8)) := #[#[0, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 7], #[0, 7], #[7]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 21)) := #[#[7], #[0], #[0], #[7], #[7], #[1]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 21 := (stabilizersData.getD i.val #[]).getD j.val 0

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

private def fullTest {k : ℕ} (M : Magma (Fin 8))
    (L : MagmaLaw (Fin k)) : Prop :=
  ∀ φ : Fin k → Fin 8, @FreeMagma.evalInMagma _ _ M φ L.lhs =
    @FreeMagma.evalInMagma _ _ M φ L.rhs

private instance {k : ℕ} (M : Magma (Fin 8)) (L : MagmaLaw (Fin k)) :
    Decidable (fullTest M L) := by unfold fullTest; infer_instance

private def law1039 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 1))) (.Leaf 1)))⟩
private theorem count1039 : Fintype.card {p : Params // fullTest (fam p) law1039} = 21 := by native_decide

private def law1052 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 2))) (.Leaf 1)))⟩
private theorem count1052 : Fintype.card {p : Params // fullTest (fam p) law1052} = 23 := by native_decide

private def law1230 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 0)) (.Leaf 2)))⟩
private theorem count1230 : Fintype.card {p : Params // fullTest (fam p) law1230} = 14 := by native_decide

private def law1234 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 2)) (.Leaf 0)))⟩
private theorem count1234 : Fintype.card {p : Params // fullTest (fam p) law1234} = 13 := by native_decide

end Magma.InvariantNonabelianAugmentedAffine7Index2Fixed1Symmetric0

open Magma.InvariantNonabelianAugmentedAffine7Index2Fixed1Symmetric0 Magma.InvariantFamily

theorem Equation1039_not_termStructuralFromFin_Equation1052_invariantFamilyCount : ¬ Law1039.TermStructuralFromFin Law1052 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => fullTest (fam p) law1052) (fun p => fullTest (fam p) law1039)
  · intro p hp φ
    exact hp (fun i => φ i.val)
  · intro p hp
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1052, count1039]
    decide

/-- info: 'Equation1039_not_termStructuralFromFin_Equation1052_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1039._native.native_decide.ax_1_1,
 count1052._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1039_not_termStructuralFromFin_Equation1052_invariantFamilyCount

theorem Equation1234_not_termStructuralFromFin_Equation1230_invariantFamilyCount : ¬ Law1234.TermStructuralFromFin Law1230 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => fullTest (fam p) law1230) (fun p => fullTest (fam p) law1234)
  · intro p hp φ
    exact hp (fun i => φ i.val)
  · intro p hp
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1230, count1234]
    decide

/-- info: 'Equation1234_not_termStructuralFromFin_Equation1230_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1230._native.native_decide.ax_1_1,
 count1234._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1234_not_termStructuralFromFin_Equation1230_invariantFamilyCount

