import equational_theories.Definability.InvariantFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianAugmentedAffine11Index2Fixed1Symmetric0

def genData : Array (Array (Fin 12)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11], #[0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7, 11], #[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11], #[0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11]]
def gen (i : Fin 4) (x : Fin 12) : Fin 12 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 12)) := #[#[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11], #[0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11], #[0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7, 11]]
def genInv (i : Fin 4) (x : Fin 12) : Fin 12 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 12)) := #[]
def probe (i : Fin 0) (x : Fin 12) : Fin 12 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 12)) := #[]
def probeInv (i : Fin 0) (x : Fin 12) : Fin 12 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 12)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11]]
def sourceRow (i : Fin 12) (x : Fin 12) : Fin 12 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 12) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 12) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [1, 0], [3, 0], [1, 2], [2, 2], [3, 2], [3, 0, 0], [0, 1, 0], [0, 1, 2, 2, 2], [3], [0, 1], [1, 1], [2, 1], [0, 3], [2, 3], [3, 3], [0, 0, 0], [1, 0, 0], [1, 1, 0], [2, 1, 0], [0, 3, 0], [2, 3, 0], [3, 3, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [3, 2, 1], [1, 1, 2], [2, 1, 2], [3, 2, 2], [0, 3, 2], [2, 3, 2], [3, 3, 2], [1, 0, 3], [3, 0, 3], [1, 2, 3], [3, 2, 3], [0, 3, 3], [2, 3, 3], [3, 3, 0, 0], [1, 0, 1, 0], [1, 0, 3, 0], [3, 2, 3, 0], [1, 0, 0, 1], [3, 0, 0, 1], [1, 1, 0, 1], [2, 1, 0, 1], [0, 0, 1, 1], [1, 0, 1, 1]]
def words (i : Fin 55) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 12 × Fin 12) := #[(0, 0), (0, 1), (0, 2), (0, 11), (11, 0), (11, 11)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 55)) := #[#[(0, 0), (1, 0), (2, 0), (1, 12), (1, 11), (1, 14), (2, 12), (2, 18), (2, 11), (1, 18), (2, 14), (3, 0)], #[(2, 28), (0, 1), (1, 1), (2, 1), (1, 16), (1, 13), (1, 28), (2, 16), (2, 43), (2, 13), (1, 43), (3, 1)], #[(1, 38), (2, 53), (0, 3), (1, 3), (2, 3), (1, 24), (1, 26), (1, 53), (2, 24), (2, 38), (2, 26), (3, 3)], #[(2, 22), (1, 40), (2, 52), (0, 5), (1, 19), (2, 19), (1, 5), (1, 22), (1, 52), (2, 5), (2, 40), (3, 5)], #[(2, 54), (2, 4), (1, 54), (2, 27), (0, 4), (1, 39), (2, 39), (1, 23), (1, 4), (1, 27), (2, 23), (3, 4)], #[(2, 35), (2, 51), (2, 10), (1, 51), (2, 21), (0, 10), (1, 47), (2, 47), (1, 35), (1, 10), (1, 21), (3, 10)], #[(1, 33), (2, 9), (2, 48), (2, 34), (1, 48), (2, 33), (0, 9), (1, 50), (2, 50), (1, 9), (1, 34), (3, 9)], #[(1, 6), (1, 30), (2, 37), (2, 45), (2, 6), (1, 45), (2, 30), (0, 6), (1, 41), (2, 41), (1, 37), (3, 6)], #[(1, 8), (1, 20), (1, 49), (2, 8), (2, 42), (2, 20), (1, 42), (2, 49), (0, 8), (1, 32), (2, 32), (3, 8)], #[(2, 7), (1, 36), (1, 31), (1, 46), (2, 36), (2, 25), (2, 31), (1, 25), (2, 46), (0, 7), (1, 7), (3, 7)], #[(1, 2), (2, 2), (1, 17), (1, 15), (1, 29), (2, 17), (2, 44), (2, 15), (1, 44), (2, 29), (0, 2), (3, 2)], #[(4, 0), (4, 1), (4, 3), (4, 5), (4, 4), (4, 10), (4, 9), (4, 6), (4, 8), (4, 7), (4, 2), (5, 0)]]
def tr (x y : Fin 12) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![2, 12, 12, 2, 2, 1]
def valuesData : Array (Array (Fin 12)) := #[#[0, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 11], #[0, 11], #[11]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 12 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 55)) := #[#[11], #[0], #[0], #[11], #[11], #[1]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 55 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 12) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 12) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 12)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
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

private def fullTest {k : ℕ} (M : Magma (Fin 12))
    (L : MagmaLaw (Fin k)) : Prop :=
  ∀ φ : Fin k → Fin 12, @FreeMagma.evalInMagma _ _ M φ L.lhs =
    @FreeMagma.evalInMagma _ _ M φ L.rhs

private instance {k : ℕ} (M : Magma (Fin 12)) (L : MagmaLaw (Fin k)) :
    Decidable (fullTest M L) := by unfold fullTest; infer_instance

private def law111 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 2)) (.Leaf 1)))⟩
private theorem count111 : Fintype.card {p : Params // fullTest (fam p) law111} = 15 := by native_decide

private def law1234 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 2)) (.Leaf 0)))⟩
private theorem count1234 : Fintype.card {p : Params // fullTest (fam p) law1234} = 13 := by native_decide

end Magma.InvariantNonabelianAugmentedAffine11Index2Fixed1Symmetric0

open Magma.InvariantNonabelianAugmentedAffine11Index2Fixed1Symmetric0 Magma.InvariantFamily

theorem Equation1234_not_termStructuralFromFin_Equation111_invariantFamilyCount : ¬ Law1234.TermStructuralFromFin Law111 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => fullTest (fam p) law111) (fun p => fullTest (fam p) law1234)
  · intro p hp φ
    exact hp (fun i => φ i.val)
  · intro p hp
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count111, count1234]
    decide

/-- info: 'Equation1234_not_termStructuralFromFin_Equation111_invariantFamilyCount' depends on axioms: [propext,
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
 count111._native.native_decide.ax_1_1,
 count1234._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1234_not_termStructuralFromFin_Equation111_invariantFamilyCount

