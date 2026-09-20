import equational_theories.Definability.CachedWordImages

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.NonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909

def genData : Array (Array (Fin 18)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 17], #[0, 9, 1, 10, 2, 11, 3, 12, 4, 13, 5, 14, 6, 15, 7, 16, 8, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17], #[0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17]]
def gen (i : Fin 5) (x : Fin 18) : Fin 18 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 18)) := #[#[16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17], #[0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 17], #[0, 9, 1, 10, 2, 11, 3, 12, 4, 13, 5, 14, 6, 15, 7, 16, 8, 17]]
def genInv (i : Fin 5) (x : Fin 18) : Fin 18 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 18)) := #[#[0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 14, 17]]
def probe (i : Fin 1) (x : Fin 18) : Fin 18 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 18)) := #[#[0, 6, 12, 1, 7, 13, 2, 8, 14, 3, 9, 15, 4, 10, 16, 5, 11, 17]]
def probeInv (i : Fin 1) (x : Fin 18) : Fin 18 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 18)) := #[#[17, 0, 0, 17, 0, 17, 17, 17, 0, 0, 17, 17, 17, 0, 17, 0, 0, 0], #[1, 17, 1, 1, 17, 1, 17, 17, 17, 1, 1, 17, 17, 17, 1, 17, 1, 1], #[2, 2, 17, 2, 2, 17, 2, 17, 17, 17, 2, 2, 17, 17, 17, 2, 17, 2], #[17, 3, 3, 17, 3, 3, 17, 3, 17, 17, 17, 3, 3, 17, 17, 17, 3, 3], #[4, 17, 4, 4, 17, 4, 4, 17, 4, 17, 17, 17, 4, 4, 17, 17, 17, 4], #[17, 5, 17, 5, 5, 17, 5, 5, 17, 5, 17, 17, 17, 5, 5, 17, 17, 5], #[17, 17, 6, 17, 6, 6, 17, 6, 6, 17, 6, 17, 17, 17, 6, 6, 17, 6], #[17, 17, 17, 7, 17, 7, 7, 17, 7, 7, 17, 7, 17, 17, 17, 7, 7, 7], #[8, 17, 17, 17, 8, 17, 8, 8, 17, 8, 8, 17, 8, 17, 17, 17, 8, 8], #[9, 9, 17, 17, 17, 9, 17, 9, 9, 17, 9, 9, 17, 9, 17, 17, 17, 9], #[17, 10, 10, 17, 17, 17, 10, 17, 10, 10, 17, 10, 10, 17, 10, 17, 17, 10], #[17, 17, 11, 11, 17, 17, 17, 11, 17, 11, 11, 17, 11, 11, 17, 11, 17, 11], #[17, 17, 17, 12, 12, 17, 17, 17, 12, 17, 12, 12, 17, 12, 12, 17, 12, 12], #[13, 17, 17, 17, 13, 13, 17, 17, 17, 13, 17, 13, 13, 17, 13, 13, 17, 13], #[17, 14, 17, 17, 17, 14, 14, 17, 17, 17, 14, 17, 14, 14, 17, 14, 14, 14], #[15, 17, 15, 17, 17, 17, 15, 15, 17, 17, 17, 15, 17, 15, 15, 17, 15, 15], #[16, 16, 17, 16, 17, 17, 17, 16, 16, 17, 17, 17, 16, 17, 16, 16, 17, 16], #[17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17]]
def sourceRow (i : Fin 18) (x : Fin 18) : Fin 18 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 18) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 18) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [0], [3], [0, 0], [1, 0], [1, 3], [3, 3], [0, 0, 0], [4, 0, 0], [0, 1, 0], [1, 1, 0], [3, 1, 3], [3, 3, 3], [4, 0, 0, 0], [0, 4, 0, 0], [0, 0, 1, 0], [3, 1, 1, 0], [0, 0, 1, 1, 1, 0], [1], [4], [4, 0], [0, 1], [1, 1], [3, 1], [4, 3], [0, 4], [3, 4], [4, 4], [0, 4, 0], [4, 4, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [3, 1, 1], [1, 3, 1], [3, 3, 1], [1, 1, 3], [4, 3, 3], [3, 4, 3], [4, 4, 3], [1, 0, 4], [4, 0, 4], [1, 3, 4], [4, 3, 4], [0, 4, 4], [3, 4, 4], [4, 4, 4], [0, 0, 0, 0], [4, 4, 0, 0], [1, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [1, 0, 4, 0], [4, 0, 4, 0], [0, 4, 4, 0], [3, 4, 4, 0], [4, 4, 4, 0], [0, 0, 0, 1], [0, 1, 0, 1], [1, 1, 0, 1], [0, 0, 1, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [3, 1, 1, 1], [1, 3, 1, 1], [3, 3, 1, 1], [1, 1, 3, 1], [3, 1, 3, 1], [3, 3, 3, 1], [4, 3, 3, 1], [1, 1, 1, 3], [3, 1, 1, 3], [3, 3, 1, 3], [4, 3, 3, 3], [3, 4, 3, 3], [4, 4, 3, 3], [1, 3, 4, 3], [4, 3, 4, 3], [0, 4, 4, 3], [3, 4, 4, 3], [4, 4, 4, 3], [1, 1, 0, 4], [4, 4, 0, 4], [1, 1, 3, 4], [4, 4, 3, 4], [1, 0, 4, 4], [4, 0, 4, 4], [1, 3, 4, 4], [4, 3, 4, 4], [0, 4, 4, 4], [3, 4, 4, 4], [0, 0, 0, 0, 0], [0, 4, 0, 0, 0], [1, 0, 4, 0, 0], [4, 0, 4, 0, 0], [3, 4, 4, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 0], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 1, 1, 1, 0], [3, 1, 1, 1, 0], [1, 3, 1, 1, 0], [3, 3, 1, 1, 0], [1, 1, 0, 4, 0], [4, 4, 0, 4, 0], [4, 0, 4, 4, 0], [1, 3, 4, 4, 0], [4, 3, 4, 4, 0], [3, 4, 4, 4, 0], [4, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 1, 0, 1], [3, 1, 1, 0, 1], [0, 1, 0, 1, 1], [1, 1, 0, 1, 1], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1], [1, 3, 1, 1, 1], [1, 1, 3, 1, 1], [1, 1, 1, 3, 1], [3, 1, 1, 3, 1], [3, 4, 3, 3, 1], [4, 4, 3, 4, 3], [4, 0, 4, 4, 3], [3, 4, 4, 0, 4], [0, 4, 4, 3, 4], [1, 1, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0], [1, 3, 1, 1, 1, 0], [1, 1, 3, 1, 1, 0], [1, 1, 0, 1, 0, 1], [1, 3, 1, 1, 0, 1], [1, 0, 1, 0, 1, 1], [0, 1, 0, 1, 1, 1]]
def words (i : Fin 136) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 18 × Fin 18) := #[(0, 0), (0, 1), (0, 3), (0, 17), (17, 0), (17, 17)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 136)) := #[#[(0, 0), (1, 0), (1, 19), (2, 0), (1, 27), (2, 22), (2, 19), (2, 46), (1, 46), (1, 18), (2, 18), (2, 17), (2, 27), (1, 22), (2, 63), (1, 17), (1, 63), (3, 0)], #[(1, 118), (0, 1), (1, 1), (1, 25), (2, 1), (1, 44), (2, 32), (2, 25), (2, 90), (1, 90), (1, 21), (2, 21), (2, 62), (2, 44), (1, 32), (2, 118), (1, 62), (3, 1)], #[(1, 71), (1, 121), (0, 3), (1, 3), (1, 20), (2, 3), (1, 41), (2, 60), (2, 20), (2, 87), (1, 87), (1, 30), (2, 30), (2, 71), (2, 41), (1, 60), (2, 121), (3, 3)], #[(2, 131), (1, 122), (1, 131), (0, 7), (1, 7), (1, 28), (2, 7), (1, 55), (2, 72), (2, 28), (2, 126), (1, 126), (1, 57), (2, 57), (2, 122), (2, 55), (1, 72), (3, 7)], #[(1, 36), (2, 120), (1, 67), (1, 120), (0, 8), (1, 47), (1, 8), (2, 47), (1, 29), (2, 36), (2, 8), (2, 83), (1, 83), (1, 84), (2, 84), (2, 67), (2, 29), (3, 8)], #[(2, 54), (1, 49), (2, 134), (1, 112), (1, 134), (0, 14), (1, 92), (1, 14), (2, 92), (1, 54), (2, 49), (2, 14), (2, 124), (1, 124), (1, 105), (2, 105), (2, 112), (3, 14)], #[(2, 103), (2, 53), (1, 98), (2, 133), (1, 103), (1, 133), (0, 13), (1, 111), (1, 13), (2, 111), (1, 53), (2, 98), (2, 13), (2, 109), (1, 109), (1, 73), (2, 73), (3, 13)], #[(2, 11), (2, 100), (2, 96), (1, 68), (2, 130), (1, 100), (1, 130), (0, 11), (1, 77), (1, 93), (2, 77), (1, 96), (2, 68), (2, 93), (2, 110), (1, 110), (1, 11), (3, 11)], #[(1, 5), (2, 5), (2, 65), (2, 48), (1, 34), (2, 119), (1, 65), (1, 119), (0, 5), (1, 42), (1, 88), (2, 42), (1, 48), (2, 34), (2, 88), (2, 56), (1, 56), (3, 5)], #[(1, 81), (1, 4), (2, 4), (2, 61), (2, 76), (1, 31), (2, 117), (1, 61), (1, 117), (0, 4), (1, 40), (1, 86), (2, 40), (1, 76), (2, 31), (2, 86), (2, 81), (3, 4)], #[(2, 107), (1, 107), (1, 9), (2, 9), (2, 115), (2, 95), (1, 58), (2, 135), (1, 115), (1, 135), (0, 9), (1, 52), (1, 108), (2, 52), (1, 95), (2, 58), (2, 108), (3, 9)], #[(2, 74), (2, 125), (1, 125), (1, 15), (2, 15), (2, 99), (2, 78), (1, 104), (2, 132), (1, 99), (1, 132), (0, 15), (1, 94), (1, 74), (2, 94), (1, 78), (2, 104), (3, 15)], #[(2, 16), (2, 75), (2, 106), (1, 106), (1, 97), (2, 97), (2, 114), (2, 80), (1, 16), (2, 129), (1, 114), (1, 129), (0, 16), (1, 123), (1, 75), (2, 123), (1, 80), (3, 16)], #[(1, 39), (2, 10), (2, 37), (2, 85), (1, 85), (1, 82), (2, 82), (2, 59), (2, 39), (1, 10), (2, 116), (1, 59), (1, 116), (0, 10), (1, 70), (1, 37), (2, 70), (3, 10)], #[(2, 12), (1, 79), (2, 50), (2, 38), (2, 127), (1, 127), (1, 69), (2, 69), (2, 102), (2, 79), (1, 50), (2, 128), (1, 102), (1, 128), (0, 12), (1, 12), (1, 38), (3, 12)], #[(1, 24), (2, 6), (1, 43), (2, 66), (2, 24), (2, 89), (1, 89), (1, 35), (2, 35), (2, 51), (2, 43), (1, 66), (2, 113), (1, 51), (1, 113), (0, 6), (1, 6), (3, 6)], #[(1, 2), (1, 26), (2, 2), (1, 45), (2, 33), (2, 26), (2, 91), (1, 91), (1, 23), (2, 23), (2, 64), (2, 45), (1, 33), (2, 101), (1, 64), (1, 101), (0, 2), (3, 2)], #[(4, 0), (4, 1), (4, 3), (4, 7), (4, 8), (4, 14), (4, 13), (4, 11), (4, 5), (4, 4), (4, 9), (4, 15), (4, 16), (4, 10), (4, 12), (4, 6), (4, 2), (5, 0)]]
def tr (x y : Fin 18) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![2, 18, 18, 2, 2, 1]
def valuesData : Array (Array (Fin 18)) := #[#[0, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 17], #[0, 17], #[17]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 18 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 136)) := #[#[17], #[0], #[0], #[17], #[17], #[1]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 136 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def imageData : Array (Array (Fin 18)) :=
  wordImageData genPerm words
def image (i : Fin 136) (x : Fin 18) : Fin 18 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 136) (x : Fin 18) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 18) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 18) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 18)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target442 : ∀ p : Params, @Equation442 (Fin 18) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.NonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909

open Magma.NonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909

theorem Equation442_not_structuralFromFin_Equation434_nonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909 : ¬ Law442.StructuralFromFin Law434 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law434.models_iff (Fin 18) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target442 p ((@Law442.models_iff (Fin 18) (fam p)).mp hp)

/-- info: 'Equation442_not_structuralFromFin_Equation434_nonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation442_not_structuralFromFin_Equation434_nonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target442._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation442_not_structuralFromFin_Equation434_nonabelianAugmentedAffine17Index2Fixed1Symmetric0Witness1909

