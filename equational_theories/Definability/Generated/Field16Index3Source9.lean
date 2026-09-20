import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field16Index3Source9

def genData : Array (Array (Fin 16)) := #[#[0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1], #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], #[0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10]]
def gen (i : Fin 3) (x : Fin 16) : Fin 16 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 16)) := #[#[0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10], #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], #[0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1]]
def genInv (i : Fin 3) (x : Fin 16) : Fin 16 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8], #[0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]]
def probe (i : Fin 2) (x : Fin 16) : Fin 16 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8], #[0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]]
def probeInv (i : Fin 2) (x : Fin 16) : Fin 16 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 16)) := #[#[0, 0, 15, 1, 15, 8, 1, 12, 0, 10, 0, 8, 0, 10, 12, 0], #[1, 1, 0, 14, 9, 14, 13, 0, 11, 1, 9, 1, 11, 1, 1, 13], #[13, 3, 2, 2, 3, 14, 13, 10, 2, 10, 2, 8, 14, 2, 2, 8], #[2, 12, 3, 3, 15, 2, 11, 12, 11, 3, 9, 3, 3, 15, 9, 3], #[11, 12, 5, 8, 4, 4, 11, 5, 4, 14, 8, 4, 4, 14, 4, 12], #[13, 10, 9, 4, 5, 5, 4, 10, 15, 5, 5, 9, 15, 5, 13, 5], #[7, 10, 9, 14, 9, 7, 6, 6, 10, 6, 6, 12, 6, 14, 6, 12], #[11, 6, 15, 8, 6, 8, 7, 7, 7, 11, 13, 7, 15, 7, 13, 7], #[8, 2, 8, 0, 8, 2, 4, 8, 8, 8, 7, 9, 7, 0, 9, 4], #[3, 9, 1, 9, 3, 9, 9, 5, 9, 9, 8, 6, 1, 6, 5, 8], #[10, 2, 10, 0, 6, 10, 10, 0, 5, 11, 10, 10, 11, 6, 5, 2], #[3, 11, 1, 11, 11, 7, 1, 11, 10, 4, 11, 11, 7, 10, 3, 4], #[12, 6, 0, 12, 12, 6, 12, 4, 3, 4, 13, 0, 12, 12, 3, 13], #[7, 13, 13, 1, 7, 13, 5, 13, 5, 2, 1, 12, 13, 13, 12, 2], #[2, 14, 14, 4, 14, 6, 14, 4, 15, 2, 1, 6, 1, 15, 14, 14], #[15, 3, 5, 15, 7, 15, 5, 15, 3, 14, 7, 0, 14, 0, 15, 15]]
def sourceRow (i : Fin 16) (x : Fin 16) : Fin 16 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 3) : Equiv.Perm (Fin 16) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 2) : Equiv.Perm (Fin 16) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 3)) := #[[], [1], [0, 1], [2, 1], [0, 0, 1], [1, 0, 1], [1, 2, 1], [2, 2, 1], [1, 0, 0, 1], [0, 1, 0, 1], [2, 1, 2, 1], [1, 2, 2, 1], [0, 1, 0, 0, 1], [2, 1, 0, 0, 1], [0, 0, 1, 0, 1], [2, 1, 2, 2, 1], [1, 0, 1, 0, 0, 0, 0, 1, 0, 1], [2], [0, 0], [1, 0], [1, 2], [2, 2], [1, 0, 0], [0, 1, 0], [2, 1, 0], [0, 1, 2], [2, 1, 2], [1, 2, 2], [0, 1, 0, 0], [2, 1, 0, 0], [0, 0, 1, 0], [1, 0, 1, 0], [1, 2, 1, 0], [2, 2, 1, 0], [0, 1, 2, 1], [0, 0, 1, 2], [1, 2, 1, 2], [2, 2, 1, 2], [0, 1, 2, 2], [2, 1, 2, 2], [0, 0, 1, 0, 0], [1, 0, 1, 0, 0], [1, 2, 1, 0, 0], [2, 2, 1, 0, 0], [1, 0, 0, 1, 0], [0, 1, 0, 1, 0], [2, 1, 2, 1, 0], [1, 2, 2, 1, 0], [1, 0, 1, 0, 1], [0, 0, 1, 2, 1], [2, 2, 1, 2, 1], [0, 1, 2, 2, 1], [1, 0, 0, 1, 2], [0, 1, 2, 1, 2], [1, 2, 2, 1, 2], [0, 0, 1, 2, 2], [1, 2, 1, 2, 2], [2, 2, 1, 2, 2], [1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [2, 1, 2, 1, 0, 0], [1, 2, 2, 1, 0, 0], [0, 1, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 1, 2, 2, 1, 0], [2, 1, 2, 2, 1, 0], [0, 0, 1, 0, 0, 1], [1, 2, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1], [1, 0, 0, 1, 2, 1], [0, 0, 1, 2, 2, 1], [1, 2, 1, 2, 2, 1], [2, 2, 1, 2, 2, 1], [0, 0, 1, 2, 1, 2], [2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0]]
def words (i : Fin 80) : List (Fin 3) := wordsData.getD i.val []
def repData : Array (Fin 16 × Fin 16) := #[(0, 0), (0, 1), (0, 2), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 80)) := #[#[(0, 0), (1, 0), (2, 0), (2, 16), (3, 0), (3, 18), (3, 16), (2, 21), (1, 16), (3, 17), (1, 21), (2, 18), (1, 18), (2, 17), (3, 21), (1, 17)], #[(1, 1), (0, 1), (2, 19), (2, 1), (3, 22), (3, 1), (2, 27), (3, 19), (3, 20), (1, 19), (2, 22), (1, 27), (2, 20), (1, 22), (1, 20), (3, 27)], #[(2, 77), (2, 73), (0, 12), (1, 77), (3, 73), (2, 12), (3, 77), (3, 72), (1, 12), (2, 72), (1, 73), (3, 62), (3, 12), (1, 62), (1, 72), (2, 62)], #[(2, 75), (2, 79), (1, 79), (0, 15), (2, 66), (3, 75), (3, 15), (3, 79), (2, 15), (1, 66), (3, 67), (1, 75), (1, 67), (3, 66), (2, 67), (1, 15)], #[(3, 74), (3, 9), (3, 49), (2, 45), (0, 9), (1, 74), (2, 74), (2, 49), (1, 9), (2, 59), (3, 45), (1, 59), (1, 49), (3, 59), (1, 45), (2, 9)], #[(3, 48), (3, 60), (2, 10), (3, 70), (1, 60), (0, 10), (2, 70), (2, 60), (2, 46), (1, 48), (1, 46), (3, 10), (3, 46), (1, 70), (2, 48), (1, 10)], #[(3, 68), (2, 14), (3, 78), (3, 50), (2, 78), (2, 68), (0, 14), (1, 78), (3, 14), (1, 64), (1, 50), (2, 64), (1, 14), (2, 50), (1, 68), (3, 64)], #[(2, 69), (3, 13), (3, 63), (3, 65), (2, 13), (2, 65), (1, 65), (0, 13), (1, 51), (3, 69), (2, 51), (1, 63), (2, 63), (1, 69), (3, 51), (1, 13)], #[(1, 2), (3, 38), (1, 28), (2, 23), (1, 23), (2, 38), (3, 28), (1, 38), (0, 2), (1, 25), (2, 25), (2, 2), (3, 25), (3, 23), (3, 2), (2, 28)], #[(3, 53), (1, 5), (2, 31), (1, 41), (2, 53), (1, 31), (1, 53), (3, 41), (1, 34), (0, 5), (2, 5), (2, 34), (3, 31), (3, 34), (2, 41), (3, 5)], #[(1, 7), (2, 37), (1, 57), (3, 33), (3, 7), (1, 33), (1, 37), (2, 33), (2, 43), (2, 57), (0, 7), (1, 43), (3, 57), (2, 7), (3, 43), (3, 37)], #[(2, 54), (1, 11), (3, 47), (1, 76), (1, 47), (3, 11), (2, 47), (1, 54), (2, 76), (2, 61), (1, 61), (0, 11), (2, 11), (3, 76), (3, 54), (3, 61)], #[(1, 4), (2, 40), (3, 30), (1, 40), (1, 35), (3, 40), (1, 30), (2, 4), (3, 55), (3, 4), (3, 35), (2, 30), (0, 4), (1, 55), (2, 55), (2, 35)], #[(2, 58), (1, 8), (1, 58), (3, 44), (3, 58), (1, 52), (2, 8), (1, 44), (3, 8), (3, 71), (2, 44), (3, 52), (1, 71), (0, 8), (2, 52), (2, 71)], #[(3, 36), (1, 6), (1, 56), (2, 6), (1, 36), (2, 56), (1, 42), (3, 6), (3, 42), (2, 36), (3, 32), (3, 56), (2, 32), (2, 42), (0, 6), (1, 32)], #[(1, 3), (3, 26), (2, 3), (1, 39), (2, 39), (1, 26), (3, 3), (1, 29), (2, 26), (3, 29), (3, 39), (3, 24), (2, 29), (2, 24), (1, 24), (0, 3)]]
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

end Magma.Field16Index3Source9

open Magma.Field16Index3Source9

theorem Equation4435_not_structuralFromFin_Equation53_field16Index3Source9 : ¬ Law4435.StructuralFromFin Law53 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law53.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation53_field16Index3Source9' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation53_field16Index3Source9._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation53_field16Index3Source9

theorem Equation4435_not_structuralFromFin_Equation430_field16Index3Source9 : ¬ Law4435.StructuralFromFin Law430 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law430.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation430_field16Index3Source9' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation430_field16Index3Source9._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation430_field16Index3Source9

theorem Equation4435_not_structuralFromFin_Equation1432_field16Index3Source9 : ¬ Law4435.StructuralFromFin Law1432 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1432.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation1432_field16Index3Source9' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4435_not_structuralFromFin_Equation1432_field16Index3Source9._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4435._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation1432_field16Index3Source9

