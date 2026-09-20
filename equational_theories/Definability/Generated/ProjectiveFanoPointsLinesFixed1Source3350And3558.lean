import equational_theories.Definability.CachedWordImages

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectiveFanoPointsLinesFixed1Source3350And3558

def genData : Array (Array (Fin 15)) := #[#[0, 1, 2, 4, 3, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 5, 6, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 13, 12, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 10, 11, 14], #[0, 2, 1, 3, 4, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 3, 4, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 13, 12, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14], #[1, 0, 2, 3, 5, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 12, 11, 13, 14]]
def gen (i : Fin 10) (x : Fin 15) : Fin 15 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 15)) := #[#[0, 1, 2, 4, 3, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 5, 6, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 13, 12, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 10, 11, 14], #[0, 2, 1, 3, 4, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 3, 4, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 13, 12, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14], #[1, 0, 2, 3, 5, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 12, 11, 13, 14]]
def genInv (i : Fin 10) (x : Fin 15) : Fin 15 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 15)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14], #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14], #[7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 14]]
def probe (i : Fin 3) (x : Fin 15) : Fin 15 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 15)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14], #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11, 12, 13, 14], #[7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 14]]
def probeInv (i : Fin 3) (x : Fin 15) : Fin 15 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 15)) := #[#[14, 2, 1, 4, 3, 6, 5, 7, 8, 9, 10, 11, 12, 13, 0], #[2, 14, 0, 5, 6, 3, 4, 7, 8, 9, 10, 11, 12, 13, 1], #[1, 0, 14, 6, 5, 4, 3, 7, 8, 9, 10, 11, 12, 13, 2], #[4, 5, 6, 14, 0, 1, 2, 7, 8, 9, 10, 11, 12, 13, 3], #[3, 6, 5, 0, 14, 2, 1, 7, 8, 9, 10, 11, 12, 13, 4], #[6, 3, 4, 1, 2, 14, 0, 7, 8, 9, 10, 11, 12, 13, 5], #[5, 4, 3, 2, 1, 0, 14, 7, 8, 9, 10, 11, 12, 13, 6], #[7, 7, 7, 7, 7, 7, 7, 14, 9, 8, 11, 10, 13, 12, 7], #[8, 8, 8, 8, 8, 8, 8, 9, 14, 7, 12, 13, 10, 11, 8], #[9, 9, 9, 9, 9, 9, 9, 8, 7, 14, 13, 12, 11, 10, 9], #[10, 10, 10, 10, 10, 10, 10, 11, 12, 13, 14, 7, 8, 9, 10], #[11, 11, 11, 11, 11, 11, 11, 10, 13, 12, 7, 14, 9, 8, 11], #[12, 12, 12, 12, 12, 12, 12, 13, 10, 11, 8, 9, 14, 7, 12], #[13, 13, 13, 13, 13, 13, 13, 12, 11, 10, 9, 8, 7, 14, 13], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
def sourceRow (i : Fin 15) (x : Fin 15) : Fin 15 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 10) : Equiv.Perm (Fin 15) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 3) : Equiv.Perm (Fin 15) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 10)) := #[[], [8], [4, 8], [5, 8], [5, 4, 8], [1, 5, 8], [1, 5, 4, 8], [8, 4, 8, 4, 8], [8, 4, 5, 1, 2, 1, 5, 4, 8], [8, 5, 1, 5, 1, 5, 8], [8, 4, 5, 1, 6, 1, 5, 4, 8], [8, 4, 5, 1, 9, 1, 5, 4, 8], [5], [5, 4], [8, 4], [1, 5], [8, 5], [1, 5, 4], [8, 5, 4], [4, 8, 4], [5, 8, 4], [8, 1, 5], [4, 8, 5], [5, 8, 5], [8, 1, 5, 4], [4, 8, 5, 4], [5, 8, 5, 4], [5, 4, 8, 4], [1, 5, 8, 4], [4, 8, 1, 5], [5, 8, 1, 5], [1, 4, 8, 5], [5, 4, 8, 5], [1, 5, 8, 5], [5, 8, 1, 5, 4], [5, 4, 8, 5, 4], [1, 5, 8, 5, 4], [1, 5, 4, 8, 4], [5, 4, 8, 1, 5], [1, 5, 8, 1, 5], [5, 1, 4, 8, 5], [1, 5, 4, 8, 5], [4, 1, 5, 8, 5], [1, 5, 8, 1, 5, 4], [1, 5, 4, 8, 5, 4], [4, 1, 5, 8, 5, 4], [9, 8], [6, 9], [7, 9], [9, 4, 8], [9, 5, 8], [6, 9, 8], [7, 9, 8], [7, 6, 9], [3, 7, 9], [9, 5, 4, 8], [6, 9, 4, 8], [7, 9, 4, 8], [9, 1, 5, 8], [6, 9, 5, 8], [7, 9, 5, 8], [7, 6, 9, 8], [3, 7, 9, 8], [3, 7, 6, 9], [9, 1, 5, 4, 8], [6, 9, 5, 4, 8], [7, 9, 5, 4, 8], [7, 6, 9, 4, 8], [3, 7, 9, 4, 8], [6, 9, 1, 5, 8], [7, 9, 1, 5, 8], [7, 6, 9, 5, 8], [3, 7, 9, 5, 8], [3, 7, 6, 9, 8], [6, 9, 1, 5, 4, 8], [7, 9, 1, 5, 4, 8], [7, 6, 9, 5, 4, 8], [3, 7, 9, 5, 4, 8], [3, 7, 6, 9, 4, 8], [7, 6, 9, 1, 5, 8], [3, 7, 9, 1, 5, 8], [3, 7, 6, 9, 5, 8], [7, 6, 9, 1, 5, 4, 8], [3, 7, 9, 1, 5, 4, 8], [3, 7, 6, 9, 5, 4, 8], [3, 7, 6, 9, 1, 5, 8], [3, 7, 6, 9, 1, 5, 4, 8], [7], [7, 6], [9, 6], [3, 7], [9, 7], [3, 7, 6], [9, 7, 6], [6, 9, 6], [7, 9, 6], [9, 3, 7], [6, 9, 7], [7, 9, 7], [9, 3, 7, 6], [6, 9, 7, 6], [7, 9, 7, 6], [7, 6, 9, 6], [3, 7, 9, 6], [6, 9, 3, 7], [7, 9, 3, 7], [3, 6, 9, 7], [7, 6, 9, 7], [3, 7, 9, 7], [7, 9, 3, 7, 6], [7, 6, 9, 7, 6], [3, 7, 9, 7, 6], [3, 7, 6, 9, 6], [7, 6, 9, 3, 7], [3, 7, 9, 3, 7], [7, 3, 6, 9, 7], [3, 7, 6, 9, 7], [6, 3, 7, 9, 7], [3, 7, 9, 3, 7, 6], [3, 7, 6, 9, 7, 6], [6, 3, 7, 9, 7, 6]]
def words (i : Fin 121) : List (Fin 10) := wordsData.getD i.val []
def repData : Array (Fin 15 × Fin 15) := #[(0, 0), (0, 1), (0, 7), (0, 14), (7, 0), (7, 7), (7, 8), (7, 14), (14, 0), (14, 7), (14, 14)]
def rep (i : Fin 11) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 11 × Fin 121)) := #[#[(0, 0), (1, 0), (1, 7), (1, 12), (1, 13), (1, 15), (1, 17), (2, 0), (2, 11), (2, 47), (2, 48), (2, 53), (2, 54), (2, 63), (3, 0)], #[(1, 1), (0, 1), (1, 14), (1, 16), (1, 21), (1, 18), (1, 24), (2, 1), (2, 46), (2, 51), (2, 52), (2, 61), (2, 62), (2, 73), (3, 1)], #[(1, 2), (1, 19), (0, 2), (1, 22), (1, 29), (1, 31), (1, 25), (2, 2), (2, 49), (2, 56), (2, 57), (2, 67), (2, 68), (2, 78), (3, 2)], #[(1, 3), (1, 23), (1, 30), (0, 3), (1, 20), (1, 26), (1, 34), (2, 3), (2, 50), (2, 59), (2, 60), (2, 71), (2, 72), (2, 81), (3, 3)], #[(1, 4), (1, 32), (1, 38), (1, 27), (0, 4), (1, 40), (1, 35), (2, 4), (2, 55), (2, 65), (2, 66), (2, 76), (2, 77), (2, 84), (3, 4)], #[(1, 5), (1, 33), (1, 39), (1, 36), (1, 43), (0, 5), (1, 28), (2, 5), (2, 58), (2, 69), (2, 70), (2, 79), (2, 80), (2, 85), (3, 5)], #[(1, 6), (1, 41), (1, 42), (1, 45), (1, 44), (1, 37), (0, 6), (2, 6), (2, 64), (2, 74), (2, 75), (2, 82), (2, 83), (2, 86), (3, 6)], #[(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (6, 0), (6, 10), (6, 87), (6, 88), (6, 90), (6, 92), (7, 0)], #[(4, 11), (4, 46), (4, 49), (4, 50), (4, 55), (4, 58), (4, 64), (6, 11), (5, 11), (6, 89), (6, 91), (6, 96), (6, 93), (6, 99), (7, 11)], #[(4, 47), (4, 51), (4, 56), (4, 59), (4, 65), (4, 69), (4, 74), (6, 47), (6, 94), (5, 47), (6, 97), (6, 104), (6, 106), (6, 100), (7, 47)], #[(4, 48), (4, 52), (4, 57), (4, 60), (4, 66), (4, 70), (4, 75), (6, 48), (6, 98), (6, 105), (5, 48), (6, 95), (6, 101), (6, 109), (7, 48)], #[(4, 53), (4, 61), (4, 67), (4, 71), (4, 76), (4, 79), (4, 82), (6, 53), (6, 107), (6, 113), (6, 102), (5, 53), (6, 115), (6, 110), (7, 53)], #[(4, 54), (4, 62), (4, 68), (4, 72), (4, 77), (4, 80), (4, 83), (6, 54), (6, 108), (6, 114), (6, 111), (6, 118), (5, 54), (6, 103), (7, 54)], #[(4, 63), (4, 73), (4, 78), (4, 81), (4, 84), (4, 85), (4, 86), (6, 63), (6, 116), (6, 117), (6, 120), (6, 119), (6, 112), (5, 63), (7, 63)], #[(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 11), (9, 47), (9, 48), (9, 53), (9, 54), (9, 63), (10, 0)]]
def tr (x y : Fin 15) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 11 → ℕ := ![2, 4, 3, 2, 3, 2, 4, 2, 2, 2, 1]
def valuesData : Array (Array (Fin 15)) := #[#[0, 14], #[0, 1, 2, 14], #[0, 7, 14], #[0, 14], #[0, 7, 14], #[7, 14], #[7, 8, 9, 14], #[7, 14], #[0, 14], #[7, 14], #[14]]
def values (i : Fin 11) (j : Fin (sizes i)) : Fin 15 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 121)) := #[#[7, 8, 9, 10, 11, 0], #[9, 8, 10, 11, 0, 0], #[7, 10, 9, 8, 0, 0], #[7, 8, 9, 10, 11, 0], #[7, 10, 9, 8, 0, 0], #[10, 9, 8, 7, 1, 0], #[8, 9, 7, 1, 0, 0], #[10, 9, 8, 7, 1, 0], #[7, 8, 9, 10, 11, 0], #[10, 9, 8, 7, 1, 0], #[9, 8, 7, 10, 1, 11]]
def stabilizers (i : Fin 11) (j : Fin 6) : Fin 121 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 11) → Fin (sizes i)
def imageData : Array (Array (Fin 15)) :=
  wordImageData genPerm words
def image (i : Fin 121) (x : Fin 15) : Fin 15 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 121) (x : Fin 15) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 15) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 15) := ⟨sourceRow⟩
def pattern : Fin 3 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 15)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target315 : ∀ p : Params, @Equation315 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target4290 : ∀ p : Params, @Equation4290 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target4297 : ∀ p : Params, @Equation4297 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target4424 : ∀ p : Params, @Equation4424 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.ProjectiveFanoPointsLinesFixed1Source3350And3558

open Magma.ProjectiveFanoPointsLinesFixed1Source3350And3558

theorem Equation315_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558 : ¬ Law315.StructuralFromFin Law3350 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3350.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target315 p ((@Law315.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation315_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation315_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target315._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation315_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558

theorem Equation4290_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558 : ¬ Law4290.StructuralFromFin Law3350 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3350.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target4290 p ((@Law4290.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation4290_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4290_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4290._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4290_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558

theorem Equation4297_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558 : ¬ Law4297.StructuralFromFin Law3350 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3350.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target4297 p ((@Law4297.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation4297_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4297_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4297._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4297_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558

theorem Equation4424_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558 : ¬ Law4424.StructuralFromFin Law3350 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3350.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target4424 p ((@Law4424.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation4424_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4424_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4424._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4424_not_structuralFromFin_Equation3350_projectiveFanoPointsLinesFixed1Source3350And3558

theorem Equation4290_not_structuralFromFin_Equation3558_projectiveFanoPointsLinesFixed1Source3350And3558 : ¬ Law4290.StructuralFromFin Law3558 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3558.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target4290 p ((@Law4290.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation4290_not_structuralFromFin_Equation3558_projectiveFanoPointsLinesFixed1Source3350And3558' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4290_not_structuralFromFin_Equation3558_projectiveFanoPointsLinesFixed1Source3350And3558._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4290._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4290_not_structuralFromFin_Equation3558_projectiveFanoPointsLinesFixed1Source3350And3558

