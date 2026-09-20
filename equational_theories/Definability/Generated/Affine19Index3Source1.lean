import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Affine19Index3Source1

def genData : Array (Array (Fin 19)) := #[#[0, 11, 3, 14, 6, 17, 9, 1, 12, 4, 15, 7, 18, 10, 2, 13, 5, 16, 8], #[0, 12, 5, 17, 10, 3, 15, 8, 1, 13, 6, 18, 11, 4, 16, 9, 2, 14, 7], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 0], #[0, 7, 14, 2, 9, 16, 4, 11, 18, 6, 13, 1, 8, 15, 3, 10, 17, 5, 12], #[0, 8, 16, 5, 13, 2, 10, 18, 7, 15, 4, 12, 1, 9, 17, 6, 14, 3, 11], #[18, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
def gen (i : Fin 6) (x : Fin 19) : Fin 19 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 19)) := #[#[0, 7, 14, 2, 9, 16, 4, 11, 18, 6, 13, 1, 8, 15, 3, 10, 17, 5, 12], #[0, 8, 16, 5, 13, 2, 10, 18, 7, 15, 4, 12, 1, 9, 17, 6, 14, 3, 11], #[18, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 11, 3, 14, 6, 17, 9, 1, 12, 4, 15, 7, 18, 10, 2, 13, 5, 16, 8], #[0, 12, 5, 17, 10, 3, 15, 8, 1, 13, 6, 18, 11, 4, 16, 9, 2, 14, 7], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 0]]
def genInv (i : Fin 6) (x : Fin 19) : Fin 19 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 19)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 17]]
def probe (i : Fin 1) (x : Fin 19) : Fin 19 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 19)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 17]]
def probeInv (i : Fin 1) (x : Fin 19) : Fin 19 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 19)) := #[#[0, 6, 0, 0, 0, 0, 0, 4, 10, 0, 0, 9, 15, 0, 0, 0, 0, 0, 13], #[14, 1, 7, 1, 1, 1, 1, 1, 5, 11, 1, 1, 10, 16, 1, 1, 1, 1, 1], #[2, 15, 2, 8, 2, 2, 2, 2, 2, 6, 12, 2, 2, 11, 17, 2, 2, 2, 2], #[3, 3, 16, 3, 9, 3, 3, 3, 3, 3, 7, 13, 3, 3, 12, 18, 3, 3, 3], #[4, 4, 4, 17, 4, 10, 4, 4, 4, 4, 4, 8, 14, 4, 4, 13, 0, 4, 4], #[5, 5, 5, 5, 18, 5, 11, 5, 5, 5, 5, 5, 9, 15, 5, 5, 14, 1, 5], #[6, 6, 6, 6, 6, 0, 6, 12, 6, 6, 6, 6, 6, 10, 16, 6, 6, 15, 2], #[3, 7, 7, 7, 7, 7, 1, 7, 13, 7, 7, 7, 7, 7, 11, 17, 7, 7, 16], #[17, 4, 8, 8, 8, 8, 8, 2, 8, 14, 8, 8, 8, 8, 8, 12, 18, 8, 8], #[9, 18, 5, 9, 9, 9, 9, 9, 3, 9, 15, 9, 9, 9, 9, 9, 13, 0, 9], #[10, 10, 0, 6, 10, 10, 10, 10, 10, 4, 10, 16, 10, 10, 10, 10, 10, 14, 1], #[2, 11, 11, 1, 7, 11, 11, 11, 11, 11, 5, 11, 17, 11, 11, 11, 11, 11, 15], #[16, 3, 12, 12, 2, 8, 12, 12, 12, 12, 12, 6, 12, 18, 12, 12, 12, 12, 12], #[13, 17, 4, 13, 13, 3, 9, 13, 13, 13, 13, 13, 7, 13, 0, 13, 13, 13, 13], #[14, 14, 18, 5, 14, 14, 4, 10, 14, 14, 14, 14, 14, 8, 14, 1, 14, 14, 14], #[15, 15, 15, 0, 6, 15, 15, 5, 11, 15, 15, 15, 15, 15, 9, 15, 2, 15, 15], #[16, 16, 16, 16, 1, 7, 16, 16, 6, 12, 16, 16, 16, 16, 16, 10, 16, 3, 16], #[17, 17, 17, 17, 17, 2, 8, 17, 17, 7, 13, 17, 17, 17, 17, 17, 11, 17, 4], #[5, 18, 18, 18, 18, 18, 3, 9, 18, 18, 8, 14, 18, 18, 18, 18, 18, 12, 18]]
def sourceRow (i : Fin 19) (x : Fin 19) : Fin 19 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 6) : Equiv.Perm (Fin 19) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 19) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 6)) := #[[], [2], [5], [0, 2], [1, 2], [2, 2], [3, 2], [4, 2], [5, 5], [5, 0, 2], [2, 1, 2], [0, 2, 2], [1, 2, 2], [3, 2, 2], [4, 2, 2], [5, 3, 2], [2, 4, 2], [0, 5, 0, 2], [4, 5, 0, 2], [5, 5, 5, 0, 2, 2], [1], [3], [4], [1, 0], [2, 0], [5, 0], [2, 1], [5, 1], [2, 3], [5, 3], [2, 4], [5, 4], [0, 5], [1, 5], [3, 5], [4, 5], [2, 1, 0], [5, 1, 0], [0, 2, 0], [1, 2, 0], [2, 2, 0], [3, 2, 0], [4, 2, 0], [0, 5, 0], [1, 5, 0], [3, 5, 0], [4, 5, 0], [5, 5, 0], [0, 2, 1], [1, 2, 1], [2, 2, 1], [3, 2, 1], [4, 2, 1], [0, 5, 1], [1, 5, 1], [3, 5, 1], [4, 5, 1], [5, 5, 1], [2, 2, 2], [2, 2, 3], [5, 5, 3], [2, 2, 4], [5, 5, 4], [2, 0, 5], [5, 1, 5], [2, 3, 5], [5, 4, 5], [0, 5, 5], [1, 5, 5], [3, 5, 5], [4, 5, 5], [5, 5, 5], [2, 2, 1, 0], [5, 5, 1, 0], [5, 0, 2, 0], [2, 1, 2, 0], [0, 2, 2, 0], [1, 2, 2, 0], [3, 2, 2, 0], [4, 2, 2, 0], [5, 3, 2, 0], [2, 4, 2, 0], [2, 0, 5, 0], [5, 1, 5, 0], [2, 3, 5, 0], [5, 4, 5, 0], [0, 5, 5, 0], [1, 5, 5, 0], [3, 5, 5, 0], [4, 5, 5, 0], [5, 0, 2, 1], [2, 1, 2, 1], [0, 2, 2, 1], [1, 2, 2, 1], [3, 2, 2, 1], [5, 3, 2, 1], [2, 4, 2, 1], [2, 0, 5, 1], [5, 1, 5, 1], [2, 3, 5, 1], [5, 4, 5, 1], [0, 5, 5, 1], [1, 5, 5, 1], [3, 5, 5, 1], [1, 2, 1, 2], [3, 2, 1, 2], [2, 2, 2, 2], [0, 2, 0, 5], [4, 2, 0, 5], [1, 5, 1, 5], [3, 5, 1, 5], [5, 5, 5, 5], [4, 5, 0, 2, 0], [4, 2, 0, 5, 0]]
def words (i : Fin 114) : List (Fin 6) := wordsData.getD i.val []
def repData : Array (Fin 19 × Fin 19) := #[(0, 0), (0, 1), (0, 2), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 114)) := #[#[(0, 0), (1, 0), (2, 0), (2, 19), (3, 0), (2, 20), (3, 19), (1, 21), (1, 22), (3, 21), (3, 20), (1, 19), (1, 20), (3, 22), (2, 21), (3, 23), (2, 22), (2, 23), (1, 23)], #[(1, 36), (0, 1), (1, 1), (2, 1), (2, 24), (3, 1), (2, 26), (3, 24), (1, 28), (1, 30), (3, 28), (3, 26), (1, 24), (1, 26), (3, 30), (2, 28), (3, 36), (2, 30), (2, 36)], #[(2, 72), (1, 72), (0, 5), (1, 5), (2, 5), (2, 40), (3, 5), (2, 50), (3, 40), (1, 59), (1, 61), (3, 59), (3, 50), (1, 40), (1, 50), (3, 61), (2, 59), (3, 72), (2, 61)], #[(2, 70), (2, 92), (1, 92), (0, 11), (1, 58), (2, 58), (2, 11), (3, 58), (2, 89), (3, 11), (1, 76), (1, 70), (3, 76), (3, 89), (1, 11), (1, 89), (3, 70), (2, 76), (3, 92)], #[(3, 112), (2, 110), (2, 112), (1, 112), (0, 18), (1, 106), (2, 106), (2, 104), (3, 106), (2, 18), (3, 104), (1, 107), (1, 110), (3, 107), (3, 18), (1, 104), (1, 18), (3, 110), (2, 107)], #[(2, 69), (3, 77), (2, 103), (2, 77), (1, 77), (0, 12), (1, 88), (2, 88), (2, 93), (3, 88), (2, 12), (3, 93), (1, 69), (1, 103), (3, 69), (3, 12), (1, 93), (1, 12), (3, 103)], #[(3, 95), (2, 15), (3, 83), (2, 95), (2, 83), (1, 83), (0, 15), (1, 80), (2, 80), (2, 98), (3, 80), (2, 64), (3, 98), (1, 15), (1, 95), (3, 15), (3, 64), (1, 98), (1, 64)], #[(1, 33), (3, 51), (2, 6), (3, 44), (2, 51), (2, 44), (1, 44), (0, 6), (1, 41), (2, 41), (2, 54), (3, 41), (2, 33), (3, 54), (1, 6), (1, 51), (3, 6), (3, 33), (1, 54)], #[(1, 32), (1, 42), (3, 7), (2, 43), (3, 53), (2, 7), (2, 53), (1, 53), (0, 7), (1, 52), (2, 52), (2, 32), (3, 52), (2, 42), (3, 32), (1, 43), (1, 7), (3, 43), (3, 42)], #[(3, 81), (1, 63), (1, 81), (3, 16), (2, 82), (3, 97), (2, 16), (2, 97), (1, 97), (0, 16), (1, 96), (2, 96), (2, 63), (3, 96), (2, 81), (3, 63), (1, 82), (1, 16), (3, 82)], #[(3, 74), (3, 85), (1, 9), (1, 85), (3, 66), (2, 74), (3, 90), (2, 66), (2, 90), (1, 90), (0, 9), (1, 100), (2, 100), (2, 9), (3, 100), (2, 85), (3, 9), (1, 74), (1, 66)], #[(1, 35), (3, 38), (3, 46), (1, 3), (1, 46), (3, 35), (2, 38), (3, 48), (2, 35), (2, 48), (1, 48), (0, 3), (1, 56), (2, 56), (2, 3), (3, 56), (2, 46), (3, 3), (1, 38)], #[(1, 34), (1, 55), (3, 34), (3, 4), (1, 49), (1, 4), (3, 55), (2, 34), (3, 39), (2, 55), (2, 39), (1, 39), (0, 4), (1, 45), (2, 45), (2, 49), (3, 45), (2, 4), (3, 49)], #[(3, 91), (1, 65), (1, 99), (3, 65), (3, 10), (1, 91), (1, 10), (3, 99), (2, 65), (3, 75), (2, 99), (2, 75), (1, 75), (0, 10), (1, 84), (2, 84), (2, 91), (3, 84), (2, 10)], #[(2, 68), (3, 102), (1, 13), (1, 94), (3, 13), (3, 68), (1, 102), (1, 68), (3, 94), (2, 13), (3, 87), (2, 94), (2, 87), (1, 87), (0, 13), (1, 78), (2, 78), (2, 102), (3, 78)], #[(3, 111), (2, 108), (3, 109), (1, 17), (1, 105), (3, 17), (3, 108), (1, 109), (1, 108), (3, 105), (2, 17), (3, 113), (2, 105), (2, 113), (1, 113), (0, 17), (1, 111), (2, 111), (2, 109)], #[(2, 67), (3, 71), (2, 79), (3, 67), (1, 86), (1, 14), (3, 86), (3, 79), (1, 67), (1, 79), (3, 14), (2, 86), (3, 101), (2, 14), (2, 101), (1, 101), (0, 14), (1, 71), (2, 71)], #[(2, 8), (2, 47), (3, 8), (2, 57), (3, 47), (1, 60), (1, 62), (3, 60), (3, 57), (1, 47), (1, 57), (3, 62), (2, 60), (3, 73), (2, 62), (2, 73), (1, 73), (0, 8), (1, 8)], #[(1, 2), (2, 2), (2, 25), (3, 2), (2, 27), (3, 25), (1, 29), (1, 31), (3, 29), (3, 27), (1, 25), (1, 27), (3, 31), (2, 29), (3, 37), (2, 31), (2, 37), (1, 37), (0, 2)]]
def tr (x y : Fin 19) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![1, 19, 19, 19]
def valuesData : Array (Array (Fin 19)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 19 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 114)) := #[#[19], #[0], #[0], #[0]]
def stabilizers (i : Fin 4) (j : Fin 1) : Fin 114 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 19) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 19) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 19)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target829 : ∀ p : Params, @Equation829 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1033 : ∀ p : Params, @Equation1033 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1227 : ∀ p : Params, @Equation1227 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1230 : ∀ p : Params, @Equation1230 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1633 : ∀ p : Params, @Equation1633 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target3460 : ∀ p : Params, @Equation3460 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target3723 : ∀ p : Params, @Equation3723 (Fin 19) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.Affine19Index3Source1

open Magma.Affine19Index3Source1

theorem Equation829_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law829.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target829 p ((@Law829.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation829_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation829_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target829._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation829_not_structuralFromFin_Equation1235_affine19Index3Source1

theorem Equation3723_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law3723.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3723 p ((@Law3723.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation3723_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3723_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3723._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3723_not_structuralFromFin_Equation1235_affine19Index3Source1

theorem Equation1033_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law1033.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1033 p ((@Law1033.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation1033_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1033_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1033._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1033_not_structuralFromFin_Equation1235_affine19Index3Source1

theorem Equation1227_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law1227.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1227 p ((@Law1227.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation1227_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1227_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1227._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1227_not_structuralFromFin_Equation1235_affine19Index3Source1

theorem Equation1230_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law1230.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1230 p ((@Law1230.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation1230_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1230_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1230._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1230_not_structuralFromFin_Equation1235_affine19Index3Source1

theorem Equation1633_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law1633.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1633 p ((@Law1633.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation1633_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1633_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1633._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1633_not_structuralFromFin_Equation1235_affine19Index3Source1

theorem Equation3460_not_structuralFromFin_Equation1235_affine19Index3Source1 : ¬ Law3460.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 19) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3460 p ((@Law3460.models_iff (Fin 19) (fam p)).mp hp)

/-- info: 'Equation3460_not_structuralFromFin_Equation1235_affine19Index3Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3460_not_structuralFromFin_Equation1235_affine19Index3Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3460._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3460_not_structuralFromFin_Equation1235_affine19Index3Source1

