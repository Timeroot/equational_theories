import equational_theories.Definability.CachedWordImages

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.NonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

def genData : Array (Array (Fin 12)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11], #[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11], #[0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11]]
def gen (i : Fin 5) (x : Fin 12) : Fin 12 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 12)) := #[#[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11], #[0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11], #[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11]]
def genInv (i : Fin 5) (x : Fin 12) : Fin 12 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 12)) := #[#[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
def probe (i : Fin 1) (x : Fin 12) : Fin 12 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 12)) := #[#[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
def probeInv (i : Fin 1) (x : Fin 12) : Fin 12 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 12)) := #[#[11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0], #[10, 11, 3, 5, 7, 9, 0, 2, 4, 6, 8, 1], #[9, 0, 11, 4, 6, 8, 10, 1, 3, 5, 7, 2], #[8, 10, 1, 11, 5, 7, 9, 0, 2, 4, 6, 3], #[7, 9, 0, 2, 11, 6, 8, 10, 1, 3, 5, 4], #[6, 8, 10, 1, 3, 11, 7, 9, 0, 2, 4, 5], #[5, 7, 9, 0, 2, 4, 11, 8, 10, 1, 3, 6], #[4, 6, 8, 10, 1, 3, 5, 11, 9, 0, 2, 7], #[3, 5, 7, 9, 0, 2, 4, 6, 11, 10, 1, 8], #[2, 4, 6, 8, 10, 1, 3, 5, 7, 11, 0, 9], #[1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 11, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11]]
def sourceRow (i : Fin 12) (x : Fin 12) : Fin 12 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 12) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 12) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [0], [3], [0, 0], [4, 0], [1, 3], [4, 3], [0, 0, 0], [1, 0, 0], [0, 4, 0], [3, 1, 3], [0, 1, 1, 3, 1, 3], [1], [4], [1, 0], [0, 1], [1, 1], [3, 1], [3, 3], [0, 4], [3, 4], [4, 4], [0, 1, 0], [1, 1, 0], [4, 4, 0], [1, 0, 1], [4, 0, 1], [0, 1, 1], [3, 1, 1], [1, 3, 1], [4, 3, 1], [1, 1, 3], [1, 3, 3], [3, 3, 3], [3, 4, 3], [4, 4, 3], [0, 0, 4], [4, 0, 4], [3, 3, 4], [4, 3, 4], [0, 4, 4], [3, 4, 4], [4, 4, 4], [0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [1, 0, 1, 0], [4, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [3, 1, 1, 0], [0, 0, 4, 0], [4, 0, 4, 0], [0, 4, 4, 0], [3, 4, 4, 0], [4, 4, 4, 0], [1, 1, 0, 1], [4, 4, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [3, 1, 1, 1], [1, 3, 1, 1], [1, 1, 3, 1], [1, 1, 1, 3], [3, 4, 4, 3], [4, 4, 4, 3], [4, 4, 0, 4], [4, 4, 3, 4], [4, 0, 4, 4], [4, 3, 4, 4], [0, 4, 4, 4], [3, 4, 4, 4], [4, 4, 4, 4], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0], [1, 3, 1, 1, 0], [4, 0, 4, 4, 0], [4, 4, 4, 4, 0], [1, 1, 1, 0, 1], [1, 1, 0, 1, 1], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1], [1, 1, 1, 1, 1], [3, 1, 1, 1, 1], [1, 3, 1, 1, 1], [1, 1, 3, 1, 1], [1, 1, 1, 3, 1], [1, 1, 1, 1, 3], [4, 3, 4, 4, 3], [4, 4, 4, 4, 3], [4, 4, 4, 0, 4], [4, 4, 4, 3, 4], [4, 4, 0, 4, 4], [4, 4, 3, 4, 4], [4, 0, 4, 4, 4], [4, 3, 4, 4, 4], [0, 4, 4, 4, 4], [3, 4, 4, 4, 4], [1, 1, 1, 1, 1, 0], [1, 1, 1, 1, 0, 1], [1, 1, 1, 0, 1, 1], [1, 1, 0, 1, 1, 1], [1, 0, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1], [1, 3, 1, 1, 1, 1], [1, 1, 3, 1, 1, 1], [1, 1, 1, 3, 1, 1], [1, 1, 1, 1, 3, 1]]
def words (i : Fin 110) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 12 × Fin 12) := #[(0, 0), (0, 1), (0, 11), (11, 0), (11, 11)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 110)) := #[#[(0, 0), (1, 0), (1, 12), (1, 21), (1, 16), (1, 61), (1, 13), (1, 42), (1, 11), (1, 74), (1, 84), (2, 0)], #[(1, 105), (0, 1), (1, 1), (1, 15), (1, 40), (1, 27), (1, 83), (1, 19), (1, 72), (1, 60), (1, 98), (2, 1)], #[(1, 91), (1, 104), (0, 3), (1, 3), (1, 14), (1, 55), (1, 25), (1, 82), (1, 36), (1, 78), (1, 59), (2, 3)], #[(1, 65), (1, 94), (1, 108), (0, 7), (1, 7), (1, 22), (1, 24), (1, 51), (1, 88), (1, 58), (1, 68), (2, 7)], #[(1, 67), (1, 57), (1, 93), (1, 103), (0, 8), (1, 43), (1, 8), (1, 54), (1, 23), (1, 81), (1, 34), (2, 8)], #[(1, 6), (1, 71), (1, 75), (1, 97), (1, 101), (0, 6), (1, 30), (1, 45), (1, 39), (1, 49), (1, 76), (2, 6)], #[(1, 89), (1, 4), (1, 70), (1, 77), (1, 96), (1, 109), (0, 4), (1, 26), (1, 44), (1, 37), (1, 47), (2, 4)], #[(1, 31), (1, 87), (1, 9), (1, 56), (1, 64), (1, 92), (1, 107), (0, 9), (1, 48), (1, 32), (1, 66), (2, 9)], #[(1, 35), (1, 46), (1, 80), (1, 52), (1, 69), (1, 50), (1, 95), (1, 102), (0, 10), (1, 33), (1, 10), (2, 10)], #[(1, 5), (1, 53), (1, 29), (1, 86), (1, 38), (1, 90), (1, 63), (1, 79), (1, 106), (0, 5), (1, 18), (2, 5)], #[(1, 2), (1, 17), (1, 41), (1, 28), (1, 85), (1, 20), (1, 73), (1, 62), (1, 99), (1, 100), (0, 2), (2, 2)], #[(3, 0), (3, 1), (3, 3), (3, 7), (3, 8), (3, 6), (3, 4), (3, 9), (3, 10), (3, 5), (3, 2), (4, 0)]]
def tr (x y : Fin 12) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![2, 12, 2, 2, 1]
def valuesData : Array (Array (Fin 12)) := #[#[0, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 11], #[0, 11], #[11]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 12 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 110)) := #[#[11], #[0], #[11], #[11], #[1]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 110 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def imageData : Array (Array (Fin 12)) :=
  wordImageData genPerm words
def image (i : Fin 110) (x : Fin 12) : Fin 12 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 110) (x : Fin 12) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 12) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 12) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 12)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target429 : ∀ p : Params, @Equation429 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target632 : ∀ p : Params, @Equation632 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1026 : ∀ p : Params, @Equation1026 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1229 : ∀ p : Params, @Equation1229 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.NonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

open Magma.NonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

theorem Equation429_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53 : ¬ Law429.StructuralFromFin Law1267 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1267.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target429 p ((@Law429.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation429_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation429_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target429._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation429_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

theorem Equation632_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53 : ¬ Law632.StructuralFromFin Law1267 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1267.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target632 p ((@Law632.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation632_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation632_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target632._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation632_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

theorem Equation1026_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53 : ¬ Law1026.StructuralFromFin Law1267 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1267.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1026 p ((@Law1026.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation1026_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1026_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target1026._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1026_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

theorem Equation1229_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53 : ¬ Law1229.StructuralFromFin Law1267 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1267.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1229 p ((@Law1229.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation1229_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1229_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target1229._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1229_not_structuralFromFin_Equation1267_nonabelianAugmentedAffine11Index1Fixed1Symmetric0Witness53

