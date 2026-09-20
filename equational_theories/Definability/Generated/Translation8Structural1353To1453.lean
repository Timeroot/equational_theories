import equational_theories.Definability.CachedWordImages
import Mathlib.Algebra.BigOperators.Fin

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Translation8Structural1353To1453

def genData : Array (Array (Fin 8)) := #[#[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[4, 5, 6, 7, 0, 1, 2, 3]]
def gen (i : Fin 3) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[4, 5, 6, 7, 0, 1, 2, 3]]
def genInv (i : Fin 3) (x : Fin 8) : Fin 8 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 8)) := #[#[0, 1, 4, 5, 2, 3, 6, 7], #[0, 4, 2, 6, 1, 5, 3, 7], #[0, 5, 6, 3, 4, 1, 2, 7], #[0, 1, 2, 3, 6, 7, 4, 5], #[0, 4, 7, 3, 1, 5, 6, 2], #[0, 1, 6, 7, 4, 5, 2, 3], #[0, 5, 2, 7, 4, 1, 6, 3], #[0, 1, 2, 3, 5, 4, 7, 6], #[0, 2, 1, 3, 4, 6, 5, 7], #[0, 2, 1, 3, 7, 5, 6, 4], #[0, 1, 7, 6, 4, 5, 3, 2], #[0, 7, 2, 5, 4, 3, 6, 1], #[0, 1, 5, 4, 3, 2, 6, 7], #[0, 6, 2, 4, 3, 5, 1, 7], #[0, 1, 2, 3, 7, 6, 5, 4], #[0, 3, 2, 1, 4, 7, 6, 5], #[0, 1, 3, 2, 4, 5, 7, 6], #[0, 3, 2, 1, 6, 5, 4, 7], #[0, 7, 4, 3, 2, 5, 6, 1], #[0, 1, 3, 2, 5, 4, 6, 7], #[0, 6, 5, 3, 4, 2, 1, 7]]
def probe (i : Fin 21) (x : Fin 8) : Fin 8 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 8)) := #[#[0, 1, 4, 5, 2, 3, 6, 7], #[0, 4, 2, 6, 1, 5, 3, 7], #[0, 5, 6, 3, 4, 1, 2, 7], #[0, 1, 2, 3, 6, 7, 4, 5], #[0, 4, 7, 3, 1, 5, 6, 2], #[0, 1, 6, 7, 4, 5, 2, 3], #[0, 5, 2, 7, 4, 1, 6, 3], #[0, 1, 2, 3, 5, 4, 7, 6], #[0, 2, 1, 3, 4, 6, 5, 7], #[0, 2, 1, 3, 7, 5, 6, 4], #[0, 1, 7, 6, 4, 5, 3, 2], #[0, 7, 2, 5, 4, 3, 6, 1], #[0, 1, 5, 4, 3, 2, 6, 7], #[0, 6, 2, 4, 3, 5, 1, 7], #[0, 1, 2, 3, 7, 6, 5, 4], #[0, 3, 2, 1, 4, 7, 6, 5], #[0, 1, 3, 2, 4, 5, 7, 6], #[0, 3, 2, 1, 6, 5, 4, 7], #[0, 7, 4, 3, 2, 5, 6, 1], #[0, 1, 3, 2, 5, 4, 6, 7], #[0, 6, 5, 3, 4, 2, 1, 7]]
def probeInv (i : Fin 21) (x : Fin 8) : Fin 8 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 8)) := #[#[2, 0, 5, 1, 3, 4, 7, 6], #[1, 3, 0, 4, 5, 2, 7, 6], #[7, 3, 0, 2, 5, 4, 1, 6], #[2, 6, 3, 1, 5, 4, 7, 0], #[7, 0, 3, 2, 6, 4, 1, 5], #[1, 6, 3, 2, 5, 7, 4, 0], #[1, 0, 5, 2, 3, 7, 4, 6], #[1, 0, 3, 4, 6, 2, 7, 5]]
def sourceRow (i : Fin 8) (x : Fin 8) : Fin 8 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 3) : Equiv.Perm (Fin 8) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 21) : Equiv.Perm (Fin 8) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 3)) := #[[], [0], [1], [2], [1, 0], [2, 0], [2, 1], [2, 1, 0]]
def words (i : Fin 8) : List (Fin 3) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]
def rep (i : Fin 8) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 8 × Fin 8)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)], #[(1, 1), (0, 1), (3, 1), (2, 1), (5, 1), (4, 1), (7, 1), (6, 1)], #[(2, 2), (3, 2), (0, 2), (1, 2), (6, 2), (7, 2), (4, 2), (5, 2)], #[(3, 4), (2, 4), (1, 4), (0, 4), (7, 4), (6, 4), (5, 4), (4, 4)], #[(4, 3), (5, 3), (6, 3), (7, 3), (0, 3), (1, 3), (2, 3), (3, 3)], #[(5, 5), (4, 5), (7, 5), (6, 5), (1, 5), (0, 5), (3, 5), (2, 5)], #[(6, 6), (7, 6), (4, 6), (5, 6), (2, 6), (3, 6), (0, 6), (1, 6)], #[(7, 7), (6, 7), (5, 7), (4, 7), (3, 7), (2, 7), (1, 7), (0, 7)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
abbrev sizes : Fin 8 → ℕ := fun _ => 8
def valuesData : Array (Array (Fin 8)) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7]]
def values (i : Fin 8) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 8)) := #[#[], #[], #[], #[], #[], #[], #[], #[]]
def stabilizers (i : Fin 8) (j : Fin 0) : Fin 8 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 8) → Fin (sizes i)
def paramEquiv : Params ≃ (Fin (8 ^ 4) × Fin (8 ^ 4)) :=
  finFunctionFinEquiv.trans (finProdFinEquiv (m := 8 ^ 4) (n := 8 ^ 4)).symm
def imageData : Array (Array (Fin 8)) :=
  wordImageData genPerm words
def image (i : Fin 8) (x : Fin 8) : Fin 8 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 8) (x : Fin 8) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 8) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 8) := ⟨sourceRow⟩
def pattern : Fin 21 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 8)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

private abbrev test1453 (p : Params) : Prop := ∀ y z : Fin 8, 0 = ((fam p).op ((fam p).op 0 y) ((fam p).op y ((fam p).op 0 z)))
private theorem restricted1453 : ∀ p : Params, test1453 p → ¬ Pattern (fam p) probePerm pattern := by
  have h : ∀ i : Fin (8 ^ 4) × Fin (8 ^ 4), test1453 (paramEquiv.symm i) →
      ¬ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by native_decide
  intro p
  simpa only [Equiv.symm_apply_apply] using h (paramEquiv p)
theorem target1453 : ∀ p : Params, @Equation1453 (Fin 8) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted1453 p (ht 0)

end Magma.Translation8Structural1353To1453

open Magma.Translation8Structural1353To1453

theorem Equation1453_not_structuralFromFin_Equation1353_translation8Structural1353To1453 : ¬ Law1453.StructuralFromFin Law1353 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1353.models_iff (Fin 8) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1453 p ((@Law1453.models_iff (Fin 8) (fam p)).mp hp)

/-- info: 'Equation1453_not_structuralFromFin_Equation1353_translation8Structural1353To1453' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1453_not_structuralFromFin_Equation1353_translation8Structural1353To1453._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted1453._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1453_not_structuralFromFin_Equation1353_translation8Structural1353To1453

