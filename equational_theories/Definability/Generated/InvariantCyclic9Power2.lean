import equational_theories.Definability.InvariantFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantCyclic9Power2

def genData : Array (Array (Fin 9)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 0], #[0, 4, 8, 3, 7, 2, 6, 1, 5], #[8, 0, 1, 2, 3, 4, 5, 6, 7], #[0, 7, 5, 3, 1, 8, 6, 4, 2]]
def gen (i : Fin 4) (x : Fin 9) : Fin 9 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 9)) := #[#[8, 0, 1, 2, 3, 4, 5, 6, 7], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[1, 2, 3, 4, 5, 6, 7, 8, 0], #[0, 4, 8, 3, 7, 2, 6, 1, 5]]
def genInv (i : Fin 4) (x : Fin 9) : Fin 9 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 9)) := #[]
def probe (i : Fin 0) (x : Fin 9) : Fin 9 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 9)) := #[]
def probeInv (i : Fin 0) (x : Fin 9) : Fin 9 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 9)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8]]
def sourceRow (i : Fin 9) (x : Fin 9) : Fin 9 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 9) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 9) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [1, 0], [3, 0], [1, 2], [0, 0, 0], [2, 3, 0], [0, 3, 2, 2, 3, 0], [3], [0, 1], [2, 1], [2, 2], [3, 2], [0, 3], [2, 3], [3, 0, 0], [2, 1, 0], [0, 0, 1], [1, 0, 1], [2, 2, 1], [0, 1, 2], [2, 2, 2], [0, 3, 2], [1, 0, 3], [1, 2, 3]]
def words (i : Fin 27) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 9 × Fin 9) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 6)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 27)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (1, 9), (2, 10), (4, 0), (1, 10), (2, 9)], #[(2, 11), (0, 1), (1, 1), (2, 1), (3, 1), (1, 11), (2, 15), (4, 1), (1, 15)], #[(1, 14), (2, 19), (0, 3), (1, 3), (2, 3), (3, 3), (1, 19), (2, 14), (4, 3)], #[(4, 7), (1, 24), (2, 18), (0, 7), (1, 7), (2, 7), (3, 7), (1, 18), (2, 24)], #[(2, 20), (4, 4), (1, 20), (2, 4), (0, 4), (1, 25), (2, 25), (3, 4), (1, 4)], #[(1, 6), (2, 17), (4, 6), (1, 17), (2, 6), (0, 6), (1, 26), (2, 26), (3, 6)], #[(3, 8), (1, 22), (2, 8), (4, 8), (1, 8), (2, 22), (0, 8), (1, 23), (2, 23)], #[(2, 13), (3, 5), (1, 21), (2, 5), (4, 5), (1, 5), (2, 21), (0, 5), (1, 13)], #[(1, 2), (2, 2), (3, 2), (1, 12), (2, 16), (4, 2), (1, 16), (2, 12), (0, 2)]]
def tr (x y : Fin 9) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![3, 9, 9, 3, 3]
def valuesData : Array (Array (Fin 9)) := #[#[0, 3, 6], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 3, 6], #[0, 3, 6]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 9 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 27)) := #[#[9], #[0], #[0], #[9], #[9]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 27 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 5) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 9) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 9) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 9)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

local instance : AddCommGroup (Fin 9) := inferInstanceAs (AddCommGroup (ZMod 9))

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

theorem translation_words : ∀ a x,
    wordPerm genPerm (List.replicate a.val 0) x = a+x := by native_decide

theorem translations (p : Params) (a) : (fam p).IsEndo (fun x => a+x) := by
  have h := word_endo (fam p) genPerm (family_generators p) (List.replicate a.val 0)
  have he : (wordPerm genPerm (List.replicate a.val 0) : _ → _) = (fun x => a+x) :=
    funext (translation_words a)
  rw [he] at h
  exact h

private def law1525 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count1525 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law1525} = 24 := by native_decide

private def law4275 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))), (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 0)))⟩
private theorem count4275 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law4275} = 18 := by native_decide

end Magma.InvariantCyclic9Power2

open Magma.InvariantCyclic9Power2 Magma.InvariantFamily

theorem Equation4275_not_termStructuralFromFin_Equation1525_invariantFamilyCount : ¬ Law4275.TermStructuralFromFin Law1525 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => ZeroTest (fam p) law1525) (fun p => ZeroTest (fam p) law4275)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (fam p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (fam p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1525, count4275]
    decide

/-- info: 'Equation4275_not_termStructuralFromFin_Equation1525_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 translation_words._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1525._native.native_decide.ax_1_1,
 count4275._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4275_not_termStructuralFromFin_Equation1525_invariantFamilyCount

