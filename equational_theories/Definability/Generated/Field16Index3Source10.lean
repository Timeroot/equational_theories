import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field16Index3Source10

def genData : Array (Array (Fin 16)) := #[#[0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1], #[1, 9, 2, 10, 7, 15, 4, 12, 13, 5, 14, 6, 11, 3, 8, 0], #[0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10], #[15, 0, 2, 13, 6, 9, 11, 4, 14, 1, 3, 12, 7, 8, 10, 5]]
def gen (i : Fin 4) (x : Fin 16) : Fin 16 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 16)) := #[#[0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10], #[15, 0, 2, 13, 6, 9, 11, 4, 14, 1, 3, 12, 7, 8, 10, 5], #[0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1], #[1, 9, 2, 10, 7, 15, 4, 12, 13, 5, 14, 6, 11, 3, 8, 0]]
def genInv (i : Fin 4) (x : Fin 16) : Fin 16 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8], #[0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]]
def probe (i : Fin 2) (x : Fin 16) : Fin 16 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8], #[0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]]
def probeInv (i : Fin 2) (x : Fin 16) : Fin 16 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 16)) := #[#[0, 11, 9, 4, 15, 8, 1, 5, 7, 10, 2, 6, 13, 14, 12, 3], #[10, 1, 5, 8, 9, 14, 4, 0, 11, 6, 7, 3, 15, 12, 2, 13], #[11, 6, 2, 9, 3, 7, 13, 10, 0, 4, 5, 8, 14, 1, 15, 12], #[7, 10, 8, 3, 6, 2, 11, 12, 5, 1, 9, 4, 0, 15, 13, 14], #[11, 12, 5, 1, 4, 15, 13, 0, 9, 10, 8, 7, 3, 14, 6, 2], #[13, 10, 0, 4, 14, 5, 1, 12, 11, 8, 6, 9, 15, 2, 3, 7], #[7, 3, 9, 14, 15, 2, 6, 13, 10, 5, 11, 8, 4, 0, 1, 12], #[2, 6, 15, 8, 3, 14, 12, 7, 4, 11, 9, 10, 1, 5, 13, 0], #[15, 2, 10, 14, 5, 6, 4, 11, 8, 3, 1, 12, 7, 0, 9, 13], #[3, 14, 15, 11, 7, 4, 10, 5, 2, 9, 13, 0, 1, 6, 12, 8], #[8, 12, 13, 0, 6, 9, 7, 4, 3, 14, 10, 1, 11, 15, 5, 2], #[13, 9, 1, 12, 8, 7, 5, 6, 15, 2, 0, 11, 14, 10, 3, 4], #[1, 2, 0, 15, 11, 6, 14, 10, 3, 4, 13, 9, 12, 7, 5, 8], #[3, 0, 14, 1, 7, 10, 11, 15, 5, 2, 8, 12, 6, 13, 9, 4], #[2, 13, 3, 0, 12, 8, 9, 4, 15, 11, 1, 6, 7, 10, 14, 5], #[12, 3, 1, 2, 9, 13, 5, 8, 10, 14, 7, 0, 11, 6, 4, 15]]
def sourceRow (i : Fin 16) (x : Fin 16) : Fin 16 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 16) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 2) : Equiv.Perm (Fin 16) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [1], [3], [0, 1], [1, 1], [2, 3], [3, 3], [0, 0, 1], [1, 0, 1], [3, 0, 1], [0, 1, 1], [3, 2, 3], [2, 3, 3], [1, 0, 0, 1], [3, 0, 0, 1], [0, 1, 0, 1], [1, 0, 1, 0, 0, 1, 0, 1], [0], [2], [0, 0], [1, 0], [3, 0], [1, 2], [3, 2], [1, 0, 0], [3, 0, 0], [0, 1, 0], [1, 1, 0], [2, 3, 0], [3, 3, 0], [0, 1, 2], [1, 1, 2], [1, 2, 2], [3, 2, 2], [2, 3, 2], [3, 3, 2], [1, 2, 3], [2, 2, 3], [0, 1, 0, 0], [1, 1, 0, 0], [2, 3, 0, 0], [3, 3, 0, 0], [0, 0, 1, 0], [1, 0, 1, 0], [3, 0, 1, 0], [0, 1, 1, 0], [1, 2, 3, 0], [3, 2, 3, 0], [2, 3, 3, 0], [1, 1, 0, 1], [0, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 2], [0, 1, 1, 2], [0, 1, 2, 2], [1, 1, 2, 2], [2, 3, 2, 2], [3, 3, 2, 2], [1, 2, 3, 2], [2, 2, 3, 2], [3, 2, 3, 2], [2, 3, 3, 2], [1, 2, 2, 3], [3, 2, 2, 3], [2, 3, 2, 3], [3, 3, 2, 3], [2, 2, 3, 3], [3, 2, 3, 3], [0, 0, 1, 0, 0], [1, 0, 1, 0, 0], [0, 1, 1, 0, 0], [1, 0, 0, 1, 0], [3, 0, 0, 1, 0], [0, 1, 0, 1, 0], [1, 1, 0, 1, 0], [0, 0, 1, 1, 0], [1, 0, 1, 1, 0], [2, 3, 2, 3, 0], [3, 2, 3, 3, 0], [3, 0, 1, 0, 1]]
def words (i : Fin 80) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 16 × Fin 16) := #[(0, 0), (0, 1), (0, 2), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 80)) := #[#[(0, 0), (1, 0), (2, 0), (2, 17), (3, 0), (3, 19), (3, 17), (2, 16), (1, 17), (3, 18), (1, 16), (2, 19), (1, 19), (2, 18), (3, 16), (1, 18)], #[(1, 22), (0, 1), (2, 1), (2, 22), (3, 20), (3, 22), (2, 24), (3, 1), (3, 32), (1, 1), (2, 20), (1, 24), (2, 32), (1, 20), (1, 32), (3, 24)], #[(2, 73), (2, 64), (0, 15), (1, 73), (3, 64), (2, 79), (3, 73), (3, 77), (1, 79), (2, 77), (1, 64), (3, 15), (3, 79), (1, 15), (1, 77), (2, 15)], #[(2, 60), (2, 74), (1, 74), (0, 11), (2, 47), (3, 60), (3, 11), (3, 74), (2, 11), (1, 47), (3, 49), (1, 60), (1, 49), (3, 47), (2, 49), (1, 11)], #[(3, 70), (3, 53), (3, 66), (2, 10), (0, 10), (1, 70), (2, 70), (2, 66), (1, 53), (2, 45), (3, 10), (1, 45), (1, 66), (3, 45), (1, 10), (2, 53)], #[(3, 35), (3, 41), (2, 6), (3, 57), (1, 41), (0, 6), (2, 57), (2, 41), (2, 29), (1, 35), (1, 29), (3, 6), (3, 29), (1, 57), (2, 35), (1, 6)], #[(3, 61), (2, 48), (3, 75), (3, 12), (2, 75), (2, 61), (0, 12), (1, 75), (3, 48), (1, 50), (1, 12), (2, 50), (1, 48), (2, 12), (1, 61), (3, 50)], #[(2, 72), (3, 63), (3, 14), (3, 76), (2, 63), (2, 76), (1, 76), (0, 14), (1, 51), (3, 72), (2, 51), (1, 14), (2, 14), (1, 72), (3, 51), (1, 63)], #[(1, 30), (3, 38), (1, 26), (2, 3), (1, 3), (2, 38), (3, 26), (1, 38), (0, 3), (1, 54), (2, 54), (2, 30), (3, 54), (3, 3), (3, 30), (2, 26)], #[(3, 39), (1, 31), (2, 4), (1, 27), (2, 39), (1, 4), (1, 39), (3, 27), (1, 55), (0, 4), (2, 31), (2, 55), (3, 4), (3, 55), (2, 27), (3, 31)], #[(1, 5), (2, 34), (1, 56), (3, 28), (3, 5), (1, 28), (1, 34), (2, 28), (2, 40), (2, 56), (0, 5), (1, 40), (3, 56), (2, 5), (3, 40), (3, 34)], #[(2, 78), (1, 62), (3, 13), (1, 67), (1, 13), (3, 62), (2, 13), (1, 78), (2, 67), (2, 71), (1, 71), (0, 13), (2, 62), (3, 67), (3, 78), (3, 71)], #[(1, 37), (2, 42), (3, 7), (1, 42), (1, 59), (3, 42), (1, 7), (2, 37), (3, 68), (3, 37), (3, 59), (2, 7), (0, 7), (1, 68), (2, 68), (2, 59)], #[(2, 43), (1, 52), (1, 43), (3, 8), (3, 43), (1, 65), (2, 52), (1, 8), (3, 52), (3, 69), (2, 8), (3, 65), (1, 69), (0, 8), (2, 65), (2, 69)], #[(3, 58), (1, 36), (1, 44), (2, 36), (1, 58), (2, 44), (1, 9), (3, 36), (3, 9), (2, 58), (3, 46), (3, 44), (2, 46), (2, 9), (0, 9), (1, 46)], #[(1, 2), (3, 23), (2, 2), (1, 33), (2, 33), (1, 23), (3, 2), (1, 25), (2, 23), (3, 25), (3, 33), (3, 21), (2, 25), (2, 21), (1, 21), (0, 2)]]
def tr (x y : Fin 16) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![1, 16, 16, 16]
def valuesData : Array (Array (Fin 16)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 16 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 80)) := #[#[16], #[0], #[0], #[0]]
def stabilizers (i : Fin 4) (j : Fin 1) : Fin 80 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 4) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 16) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 16) := ⟨sourceRow⟩
def pattern : Fin 2 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 16)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target4435 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation4435 (Fin 16) (fam p) := by native_decide

end Magma.Field16Index3Source10

open Magma.Field16Index3Source10

theorem Equation4435_not_structuralFromFin_Equation75_field16Index3Source10 : ¬ Law4435.StructuralFromFin Law75 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law75.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation75_field16Index3Source10' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation75_field16Index3Source10._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation75_field16Index3Source10

theorem Equation4435_not_structuralFromFin_Equation510_field16Index3Source10 : ¬ Law4435.StructuralFromFin Law510 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law510.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation510_field16Index3Source10' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation510_field16Index3Source10._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation510_field16Index3Source10

theorem Equation4435_not_structuralFromFin_Equation716_field16Index3Source10 : ¬ Law4435.StructuralFromFin Law716 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law716.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation716_field16Index3Source10' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation716_field16Index3Source10._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation716_field16Index3Source10

