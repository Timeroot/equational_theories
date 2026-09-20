import equational_theories.Definability.InvariantFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantCount13Index4

def genData : Array (Array (Fin 13)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0], #[0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10], #[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4]]
def gen (i : Fin 4) (x : Fin 13) : Fin 13 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 13)) := #[#[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0], #[0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10]]
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

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [1, 0], [3, 0], [1, 2], [2, 2], [3, 2], [1, 0, 0], [3, 0, 0], [2, 3, 0], [1, 2, 2], [0, 0, 3, 2, 2, 3, 0], [3], [0, 1], [2, 1], [0, 3], [2, 3], [0, 0, 0], [0, 1, 0], [2, 1, 0], [0, 3, 0], [1, 0, 1], [3, 0, 1], [2, 2, 1], [3, 2, 1], [2, 1, 2], [2, 2, 2], [0, 0, 3], [2, 2, 3], [2, 1, 0, 0], [0, 3, 0, 0], [3, 2, 1, 0], [2, 2, 3, 0], [2, 3, 0, 1], [2, 2, 1, 2], [1, 0, 0, 3], [1, 2, 2, 3]]
def words (i : Fin 39) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 13 × Fin 13) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 7)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 39)) := #[#[(0, 0), (1, 0), (2, 0), (1, 13), (3, 0), (2, 14), (2, 13), (4, 0), (4, 13), (1, 14), (3, 14), (4, 14), (3, 13)], #[(3, 15), (0, 1), (1, 1), (2, 1), (1, 15), (3, 1), (2, 17), (2, 15), (4, 1), (4, 15), (1, 17), (3, 17), (4, 17)], #[(4, 29), (3, 21), (0, 3), (1, 3), (2, 3), (1, 21), (3, 3), (2, 29), (2, 21), (4, 3), (4, 21), (1, 29), (3, 29)], #[(3, 23), (4, 23), (3, 4), (0, 4), (1, 19), (2, 19), (1, 4), (3, 19), (2, 23), (2, 4), (4, 19), (4, 4), (1, 23)], #[(1, 8), (3, 8), (4, 8), (3, 20), (0, 8), (1, 26), (2, 26), (1, 20), (3, 26), (2, 8), (2, 20), (4, 26), (4, 20)], #[(4, 31), (1, 10), (3, 10), (4, 10), (3, 31), (0, 10), (1, 33), (2, 33), (1, 31), (3, 33), (2, 10), (2, 31), (4, 33)], #[(4, 37), (4, 9), (1, 32), (3, 32), (4, 32), (3, 9), (0, 9), (1, 37), (2, 37), (1, 9), (3, 37), (2, 32), (2, 9)], #[(2, 12), (4, 38), (4, 12), (1, 34), (3, 34), (4, 34), (3, 12), (0, 12), (1, 38), (2, 38), (1, 12), (3, 38), (2, 34)], #[(2, 11), (2, 36), (4, 35), (4, 36), (1, 11), (3, 11), (4, 11), (3, 36), (0, 11), (1, 35), (2, 35), (1, 36), (3, 35)], #[(3, 24), (2, 5), (2, 27), (4, 24), (4, 27), (1, 5), (3, 5), (4, 5), (3, 27), (0, 5), (1, 24), (2, 24), (1, 27)], #[(1, 6), (3, 28), (2, 22), (2, 6), (4, 28), (4, 6), (1, 22), (3, 22), (4, 22), (3, 6), (0, 6), (1, 28), (2, 28)], #[(2, 7), (1, 25), (3, 7), (2, 30), (2, 25), (4, 7), (4, 25), (1, 30), (3, 30), (4, 30), (3, 25), (0, 7), (1, 7)], #[(1, 2), (2, 2), (1, 16), (3, 2), (2, 18), (2, 16), (4, 2), (4, 16), (1, 18), (3, 18), (4, 18), (3, 16), (0, 2)]]
def tr (x y : Fin 13) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![1, 13, 13, 13, 13]
def valuesData : Array (Array (Fin 13)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 13 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 39)) := #[#[13], #[0], #[0], #[0], #[0]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 39 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 13) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 13) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 13)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

local instance : AddCommGroup (Fin 13) := inferInstanceAs (AddCommGroup (ZMod 13))

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

private def law48 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 1))))⟩
private theorem count48 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law48} = 1549 := by native_decide

private def law412 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 1)))))⟩
private theorem count412 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law412} = 2197 := by native_decide

private def law1022 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 1))) (.Leaf 0)))⟩
private theorem count1022 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law1022} = 1318 := by native_decide

private def law3254 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 1))))⟩
private theorem count3254 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law3254} = 1549 := by native_decide

end Magma.InvariantCount13Index4

open Magma.InvariantCount13Index4 Magma.InvariantFamily

theorem Equation1022_not_termStructuralFromFin_Equation48_invariantFamilyCount : ¬ Law1022.TermStructuralFromFin Law48 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => ZeroTest (fam p) law48) (fun p => ZeroTest (fam p) law1022)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (fam p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (fam p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count48, count1022]
    decide

/-- info: 'Equation1022_not_termStructuralFromFin_Equation48_invariantFamilyCount' depends on axioms: [propext, Classical.choice, Quot.sound, coherent_values._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, same_orbit._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, tr_rep._native.native_decide.ax_1_1, translation_words._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1, values_injective._native.native_decide.ax_1_1, words_zero._native.native_decide.ax_1_1, count1022._native.native_decide.ax_1_1, count48._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1022_not_termStructuralFromFin_Equation48_invariantFamilyCount

theorem Equation3254_not_termStructuralFromFin_Equation412_invariantFamilyCount : ¬ Law3254.TermStructuralFromFin Law412 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => ZeroTest (fam p) law412) (fun p => ZeroTest (fam p) law3254)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (fam p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (fam p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count412, count3254]
    decide

/-- info: 'Equation3254_not_termStructuralFromFin_Equation412_invariantFamilyCount' depends on axioms: [propext, Classical.choice, Quot.sound, coherent_values._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, same_orbit._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, tr_rep._native.native_decide.ax_1_1, translation_words._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1, values_injective._native.native_decide.ax_1_1, words_zero._native.native_decide.ax_1_1, count3254._native.native_decide.ax_1_1, count412._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3254_not_termStructuralFromFin_Equation412_invariantFamilyCount

