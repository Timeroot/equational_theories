import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field16Index3Source12

def genData : Array (Array (Fin 16)) := #[#[0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8], #[1, 13, 10, 6, 4, 8, 15, 3, 11, 7, 0, 12, 14, 2, 5, 9], #[0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12], #[10, 0, 13, 7, 4, 14, 3, 9, 5, 15, 2, 8, 11, 1, 12, 6]]
def gen (i : Fin 4) (x : Fin 16) : Fin 16 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 16)) := #[#[0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12], #[10, 0, 13, 7, 4, 14, 3, 9, 5, 15, 2, 8, 11, 1, 12, 6], #[0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8], #[1, 13, 10, 6, 4, 8, 15, 3, 11, 7, 0, 12, 14, 2, 5, 9]]
def genInv (i : Fin 4) (x : Fin 16) : Fin 16 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8], #[0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]]
def probe (i : Fin 2) (x : Fin 16) : Fin 16 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8], #[0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]]
def probeInv (i : Fin 2) (x : Fin 16) : Fin 16 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 16)) := #[#[0, 9, 0, 0, 14, 4, 9, 0, 4, 5, 5, 0, 6, 0, 6, 14], #[8, 1, 1, 1, 5, 15, 1, 8, 4, 5, 1, 4, 1, 7, 15, 7], #[2, 2, 2, 11, 11, 2, 12, 6, 7, 2, 6, 7, 4, 12, 4, 2], #[3, 3, 10, 3, 3, 10, 7, 13, 3, 6, 6, 7, 13, 5, 3, 5], #[10, 0, 13, 4, 4, 13, 4, 4, 2, 4, 2, 10, 0, 1, 1, 4], #[1, 11, 5, 12, 12, 5, 5, 5, 5, 3, 11, 3, 0, 1, 5, 0], #[15, 6, 8, 2, 6, 6, 6, 15, 0, 8, 0, 6, 3, 6, 2, 3], #[7, 14, 3, 9, 7, 7, 14, 7, 9, 1, 7, 1, 7, 2, 2, 3], #[12, 13, 13, 8, 14, 8, 14, 6, 8, 1, 8, 8, 6, 12, 1, 8], #[12, 13, 9, 12, 9, 15, 7, 15, 0, 9, 9, 9, 13, 7, 9, 0], #[15, 10, 14, 15, 12, 4, 12, 10, 10, 10, 10, 3, 3, 10, 4, 14], #[11, 14, 14, 15, 5, 13, 11, 13, 11, 11, 2, 11, 11, 2, 15, 5], #[10, 12, 10, 2, 8, 9, 9, 12, 2, 8, 5, 12, 12, 5, 12, 12], #[13, 11, 3, 11, 8, 9, 13, 8, 9, 3, 13, 4, 4, 13, 13, 13], #[8, 0, 8, 14, 11, 14, 10, 11, 7, 14, 0, 10, 14, 14, 14, 7], #[1, 9, 15, 9, 15, 10, 10, 11, 15, 6, 11, 1, 15, 15, 6, 15]]
def sourceRow (i : Fin 16) (x : Fin 16) : Fin 16 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 16) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 2) : Equiv.Perm (Fin 16) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [1], [3], [0, 1], [1, 1], [2, 3], [3, 3], [0, 0, 1], [1, 0, 1], [3, 0, 1], [0, 1, 1], [3, 2, 3], [2, 3, 3], [1, 0, 0, 1], [3, 0, 0, 1], [0, 1, 0, 1], [1, 0, 1, 0, 0, 1, 0, 1], [0], [2], [0, 0], [1, 0], [3, 0], [1, 2], [3, 2], [1, 0, 0], [3, 0, 0], [0, 1, 0], [1, 1, 0], [2, 3, 0], [3, 3, 0], [0, 1, 2], [1, 1, 2], [1, 2, 2], [3, 2, 2], [2, 3, 2], [3, 3, 2], [1, 2, 3], [2, 2, 3], [0, 1, 0, 0], [1, 1, 0, 0], [2, 3, 0, 0], [3, 3, 0, 0], [0, 0, 1, 0], [1, 0, 1, 0], [3, 0, 1, 0], [0, 1, 1, 0], [1, 2, 3, 0], [3, 2, 3, 0], [2, 3, 3, 0], [1, 1, 0, 1], [0, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 2], [0, 1, 1, 2], [0, 1, 2, 2], [1, 1, 2, 2], [2, 3, 2, 2], [3, 3, 2, 2], [1, 2, 3, 2], [2, 2, 3, 2], [3, 2, 3, 2], [2, 3, 3, 2], [1, 2, 2, 3], [3, 2, 2, 3], [2, 3, 2, 3], [3, 3, 2, 3], [2, 2, 3, 3], [3, 2, 3, 3], [0, 0, 1, 0, 0], [1, 0, 1, 0, 0], [0, 1, 1, 0, 0], [1, 0, 0, 1, 0], [3, 0, 0, 1, 0], [0, 1, 0, 1, 0], [1, 1, 0, 1, 0], [0, 0, 1, 1, 0], [1, 0, 1, 1, 0], [2, 3, 2, 3, 0], [3, 2, 3, 3, 0], [3, 0, 1, 0, 1]]
def words (i : Fin 80) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 16 × Fin 16) := #[(0, 0), (0, 1), (0, 2), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 80)) := #[#[(0, 0), (1, 0), (2, 0), (2, 16), (3, 0), (3, 17), (3, 16), (2, 18), (1, 16), (3, 19), (1, 18), (2, 17), (1, 17), (2, 19), (3, 18), (1, 19)], #[(1, 22), (0, 1), (2, 24), (2, 22), (3, 1), (3, 22), (2, 32), (3, 24), (3, 20), (1, 24), (2, 1), (1, 32), (2, 20), (1, 1), (1, 20), (3, 32)], #[(2, 41), (2, 6), (0, 6), (1, 41), (3, 6), (2, 29), (3, 41), (3, 57), (1, 29), (2, 57), (1, 6), (3, 35), (3, 29), (1, 35), (1, 57), (2, 35)], #[(2, 10), (2, 70), (1, 70), (0, 10), (2, 45), (3, 10), (3, 66), (3, 70), (2, 66), (1, 45), (3, 53), (1, 10), (1, 53), (3, 45), (2, 53), (1, 66)], #[(3, 73), (3, 64), (3, 79), (2, 15), (0, 15), (1, 73), (2, 73), (2, 79), (1, 64), (2, 77), (3, 15), (1, 77), (1, 79), (3, 77), (1, 15), (2, 64)], #[(3, 60), (3, 74), (2, 49), (3, 47), (1, 74), (0, 11), (2, 47), (2, 74), (2, 11), (1, 60), (1, 11), (3, 49), (3, 11), (1, 47), (2, 60), (1, 49)], #[(3, 72), (2, 51), (3, 76), (3, 63), (2, 76), (2, 72), (0, 14), (1, 76), (3, 51), (1, 14), (1, 63), (2, 14), (1, 51), (2, 63), (1, 72), (3, 14)], #[(2, 50), (3, 48), (3, 61), (3, 75), (2, 48), (2, 75), (1, 75), (0, 12), (1, 12), (3, 50), (2, 12), (1, 61), (2, 61), (1, 50), (3, 12), (1, 48)], #[(1, 5), (3, 34), (1, 28), (2, 56), (1, 56), (2, 34), (3, 28), (1, 34), (0, 5), (1, 40), (2, 40), (2, 5), (3, 40), (3, 56), (3, 5), (2, 28)], #[(3, 78), (1, 62), (2, 67), (1, 13), (2, 78), (1, 67), (1, 78), (3, 13), (1, 71), (0, 13), (2, 62), (2, 71), (3, 67), (3, 71), (2, 13), (3, 62)], #[(1, 2), (2, 25), (1, 23), (3, 33), (3, 2), (1, 33), (1, 25), (2, 33), (2, 21), (2, 23), (0, 2), (1, 21), (3, 23), (2, 2), (3, 21), (3, 25)], #[(2, 9), (1, 36), (3, 44), (1, 58), (1, 44), (3, 36), (2, 44), (1, 9), (2, 58), (2, 46), (1, 46), (0, 9), (2, 36), (3, 58), (3, 9), (3, 46)], #[(1, 30), (2, 3), (3, 38), (1, 3), (1, 26), (3, 3), (1, 38), (2, 30), (3, 54), (3, 30), (3, 26), (2, 38), (0, 3), (1, 54), (2, 54), (2, 26)], #[(2, 4), (1, 31), (1, 4), (3, 39), (3, 4), (1, 27), (2, 31), (1, 39), (3, 31), (3, 55), (2, 39), (3, 27), (1, 55), (0, 4), (2, 27), (2, 55)], #[(3, 43), (1, 52), (1, 65), (2, 52), (1, 43), (2, 65), (1, 8), (3, 52), (3, 8), (2, 43), (3, 69), (3, 65), (2, 69), (2, 8), (0, 8), (1, 69)], #[(1, 37), (3, 42), (2, 37), (1, 59), (2, 59), (1, 42), (3, 37), (1, 7), (2, 42), (3, 7), (3, 59), (3, 68), (2, 7), (2, 68), (1, 68), (0, 7)]]
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

end Magma.Field16Index3Source12

open Magma.Field16Index3Source12

theorem Equation4435_not_structuralFromFin_Equation640_field16Index3Source12 : ¬ Law4435.StructuralFromFin Law640 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law640.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation640_field16Index3Source12' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation640_field16Index3Source12._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation640_field16Index3Source12

