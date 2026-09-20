import equational_theories.Definability.CachedWordImages

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectiveFanoPointsLinesFixed1Source3583

def genData : Array (Array (Fin 15)) := #[#[0, 1, 2, 4, 3, 6, 5, 11, 8, 13, 10, 7, 12, 9, 14], #[0, 1, 2, 5, 6, 3, 4, 7, 12, 13, 10, 11, 8, 9, 14], #[0, 2, 1, 3, 4, 6, 5, 9, 8, 7, 10, 13, 12, 11, 14], #[0, 3, 4, 1, 2, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14], #[1, 0, 2, 3, 5, 4, 6, 8, 7, 9, 10, 12, 11, 13, 14]]
def gen (i : Fin 5) (x : Fin 15) : Fin 15 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 15)) := #[#[0, 1, 2, 4, 3, 6, 5, 11, 8, 13, 10, 7, 12, 9, 14], #[0, 1, 2, 5, 6, 3, 4, 7, 12, 13, 10, 11, 8, 9, 14], #[0, 2, 1, 3, 4, 6, 5, 9, 8, 7, 10, 13, 12, 11, 14], #[0, 3, 4, 1, 2, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14], #[1, 0, 2, 3, 5, 4, 6, 8, 7, 9, 10, 12, 11, 13, 14]]
def genInv (i : Fin 5) (x : Fin 15) : Fin 15 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 15)) := #[#[0, 1, 2, 4, 3, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14]]
def probe (i : Fin 1) (x : Fin 15) : Fin 15 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 15)) := #[#[0, 1, 2, 4, 3, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14]]
def probeInv (i : Fin 1) (x : Fin 15) : Fin 15 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 15)) := #[#[0, 1, 2, 3, 4, 5, 6, 0, 14, 0, 14, 0, 14, 0, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 1, 1, 14, 14, 1, 1, 14], #[0, 1, 2, 3, 4, 5, 6, 2, 2, 14, 14, 2, 2, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 3, 3, 3, 3, 14], #[0, 1, 2, 3, 4, 5, 6, 4, 14, 4, 4, 14, 4, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 5, 5, 5, 5, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 6, 6, 14, 6, 14, 14, 6, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14], #[0, 1, 2, 3, 4, 5, 6, 14, 14, 14, 14, 14, 14, 14, 14]]
def sourceRow (i : Fin 15) (x : Fin 15) : Fin 15 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 15) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 15) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [4], [2, 4], [3, 4], [3, 2, 4], [1, 3, 4], [1, 3, 2, 4], [4, 2, 4, 2, 4], [4, 3, 1, 2, 1, 3, 2, 4], [4, 2, 3, 1, 4, 1, 3, 2, 4], [3, 2], [4, 2], [1, 3], [4, 3], [1, 3, 2], [4, 3, 2], [2, 4, 2], [3, 4, 2], [4, 1, 3], [2, 4, 3], [3, 4, 3], [4, 1, 3, 2], [2, 4, 3, 2], [3, 4, 3, 2], [3, 2, 4, 2], [1, 3, 4, 2], [2, 4, 1, 3], [3, 4, 1, 3], [1, 2, 4, 3], [3, 2, 4, 3], [1, 3, 4, 3], [3, 4, 1, 3, 2], [3, 2, 4, 3, 2], [1, 3, 4, 3, 2], [1, 3, 2, 4, 2], [3, 2, 4, 1, 3], [1, 3, 4, 1, 3], [3, 1, 2, 4, 3], [1, 3, 2, 4, 3], [2, 1, 3, 4, 3], [1, 3, 4, 1, 3, 2], [1, 3, 2, 4, 3, 2], [2, 1, 3, 4, 3, 2], [3, 1, 4, 2, 4, 1, 2, 4, 3], [2, 0], [4, 0], [4, 2, 0], [2, 4, 0], [3, 4, 0], [2, 4, 2, 0], [3, 4, 2, 0], [3, 2, 4, 0], [1, 3, 4, 0], [3, 2, 4, 2, 0], [1, 3, 4, 2, 0], [1, 3, 2, 4, 0], [2, 1, 3, 4, 2], [4, 1], [2, 4, 1], [3, 4, 1], [3, 2, 4, 1], [1, 3, 4, 1], [2, 1, 3, 4], [3, 4, 3, 1, 2, 1, 3, 2, 4, 3], [3, 0], [3, 2, 0], [1, 3, 0], [2, 1, 3], [0, 4, 2, 4, 0], [3, 1, 4, 3, 0, 3, 4, 1, 3], [1, 0], [2, 1], [1, 2], [4, 1, 0], [4, 2, 1], [4, 1, 2], [1, 2, 4], [2, 4, 1, 2], [3, 4, 1, 2], [3, 2, 4, 1, 2]]
def words (i : Fin 80) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 15 × Fin 15) := #[(0, 0), (0, 1), (0, 7), (0, 8), (0, 14), (7, 0), (7, 1), (7, 7), (7, 8), (7, 14), (14, 0), (14, 7), (14, 14)]
def rep (i : Fin 13) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 13 × Fin 80)) := #[#[(0, 0), (1, 0), (1, 7), (1, 9), (1, 10), (1, 12), (1, 14), (2, 0), (3, 0), (2, 7), (3, 9), (2, 43), (3, 8), (2, 44), (4, 0)], #[(1, 1), (0, 1), (1, 11), (1, 13), (1, 18), (1, 15), (1, 21), (3, 1), (2, 1), (2, 11), (3, 13), (3, 57), (2, 45), (2, 46), (4, 1)], #[(1, 2), (1, 16), (0, 2), (1, 19), (1, 26), (1, 28), (1, 22), (2, 16), (2, 2), (3, 2), (3, 19), (2, 49), (2, 47), (3, 58), (4, 2)], #[(1, 3), (1, 20), (1, 27), (0, 3), (1, 17), (1, 23), (1, 31), (3, 3), (3, 20), (3, 59), (2, 3), (2, 17), (2, 48), (2, 50), (4, 3)], #[(1, 4), (1, 29), (1, 35), (1, 24), (0, 4), (1, 37), (1, 32), (2, 24), (3, 29), (2, 53), (2, 4), (3, 4), (2, 51), (3, 60), (4, 4)], #[(1, 5), (1, 30), (1, 36), (1, 33), (1, 40), (0, 5), (1, 25), (3, 5), (2, 52), (2, 54), (2, 5), (2, 25), (3, 30), (3, 61), (4, 5)], #[(1, 6), (1, 38), (1, 39), (1, 42), (1, 41), (1, 34), (0, 6), (2, 34), (2, 55), (3, 62), (2, 6), (3, 6), (3, 38), (2, 56), (4, 6)], #[(5, 0), (6, 0), (5, 16), (6, 9), (5, 24), (6, 12), (5, 34), (7, 0), (8, 0), (8, 16), (8, 9), (8, 24), (8, 8), (8, 68), (9, 0)], #[(6, 1), (5, 1), (5, 2), (6, 13), (6, 18), (5, 52), (5, 55), (8, 1), (7, 1), (8, 2), (8, 13), (8, 57), (8, 33), (8, 58), (9, 1)], #[(5, 7), (5, 11), (6, 7), (6, 64), (5, 53), (5, 54), (6, 67), (8, 11), (8, 7), (7, 7), (8, 64), (8, 74), (8, 71), (8, 79), (9, 7)], #[(6, 3), (6, 20), (6, 27), (5, 3), (5, 4), (5, 5), (5, 6), (8, 3), (8, 20), (8, 59), (7, 3), (8, 4), (8, 30), (8, 60), (9, 3)], #[(5, 43), (6, 43), (5, 49), (5, 17), (6, 10), (5, 25), (6, 14), (8, 17), (8, 43), (8, 49), (8, 10), (7, 43), (8, 70), (8, 77), (9, 43)], #[(6, 45), (5, 45), (5, 47), (5, 48), (5, 51), (6, 15), (6, 21), (8, 45), (8, 23), (8, 47), (8, 15), (8, 73), (7, 45), (8, 76), (9, 45)], #[(5, 44), (5, 46), (6, 44), (5, 50), (6, 65), (6, 66), (5, 56), (8, 46), (8, 44), (8, 78), (8, 65), (8, 75), (8, 72), (7, 44), (9, 44)], #[(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (11, 0), (11, 1), (11, 7), (11, 3), (11, 43), (11, 45), (11, 44), (12, 0)]]
def tr (x y : Fin 15) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 13 → ℕ := ![2, 5, 3, 3, 2, 3, 3, 2, 5, 2, 2, 2, 1]
def valuesData : Array (Array (Fin 15)) := #[#[0, 14], #[0, 1, 2, 10, 14], #[0, 7, 14], #[0, 8, 14], #[0, 14], #[0, 7, 14], #[1, 7, 14], #[7, 14], #[3, 7, 8, 9, 14], #[7, 14], #[0, 14], #[7, 14], #[14]]
def values (i : Fin 13) (j : Fin (sizes i)) : Fin 15 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 80)) := #[#[7, 8, 9], #[43, 8, 0], #[8, 9, 0], #[44, 63, 0], #[7, 8, 9], #[8, 9, 0], #[68, 69, 0], #[8, 9, 16], #[63, 69, 0], #[8, 9, 16], #[7, 8, 9], #[8, 9, 16], #[43, 9, 1]]
def stabilizers (i : Fin 13) (j : Fin 3) : Fin 80 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 13) → Fin (sizes i)
def imageData : Array (Array (Fin 15)) :=
  wordImageData genPerm words
def image (i : Fin 80) (x : Fin 15) : Fin 15 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 80) (x : Fin 15) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 15) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 15) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 15)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target716 : ∀ p : Params, @Equation716 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.ProjectiveFanoPointsLinesFixed1Source3583

open Magma.ProjectiveFanoPointsLinesFixed1Source3583

theorem Equation716_not_structuralFromFin_Equation3583_projectiveFanoPointsLinesFixed1Source3583 : ¬ Law716.StructuralFromFin Law3583 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3583.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target716 p ((@Law716.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation716_not_structuralFromFin_Equation3583_projectiveFanoPointsLinesFixed1Source3583' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation716_not_structuralFromFin_Equation3583_projectiveFanoPointsLinesFixed1Source3583._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target716._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation716_not_structuralFromFin_Equation3583_projectiveFanoPointsLinesFixed1Source3583

