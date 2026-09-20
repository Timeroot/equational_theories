import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Affine5Symmetric3

def genData : Array (Array (Fin 15)) := #[#[0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13], #[0, 1, 2, 6, 7, 8, 12, 13, 14, 3, 4, 5, 9, 10, 11], #[1, 0, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11, 13, 12, 14], #[3, 4, 5, 0, 1, 2, 12, 13, 14, 9, 10, 11, 6, 7, 8], #[0, 1, 2, 9, 10, 11, 3, 4, 5, 12, 13, 14, 6, 7, 8]]
def gen (i : Fin 5) (x : Fin 15) : Fin 15 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 15)) := #[#[0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13], #[0, 1, 2, 9, 10, 11, 3, 4, 5, 12, 13, 14, 6, 7, 8], #[1, 0, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11, 13, 12, 14], #[3, 4, 5, 0, 1, 2, 12, 13, 14, 9, 10, 11, 6, 7, 8], #[0, 1, 2, 6, 7, 8, 12, 13, 14, 3, 4, 5, 9, 10, 11]]
def genInv (i : Fin 5) (x : Fin 15) : Fin 15 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 15)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 9, 10, 11]]
def probe (i : Fin 1) (x : Fin 15) : Fin 15 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 15)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 9, 10, 11]]
def probeInv (i : Fin 1) (x : Fin 15) : Fin 15 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 15)) := #[#[0, 1, 2, 3, 13, 14, 6, 10, 11, 9, 7, 8, 12, 4, 5], #[0, 1, 2, 12, 4, 14, 9, 7, 11, 6, 10, 8, 3, 13, 5], #[0, 1, 2, 12, 13, 5, 9, 10, 8, 6, 7, 11, 3, 4, 14], #[0, 7, 8, 3, 4, 5, 6, 1, 2, 9, 13, 14, 12, 10, 11], #[6, 1, 8, 3, 4, 5, 0, 7, 2, 12, 10, 14, 9, 13, 11], #[6, 7, 2, 3, 4, 5, 0, 1, 8, 12, 13, 11, 9, 10, 14], #[0, 13, 14, 3, 10, 11, 6, 7, 8, 9, 4, 5, 12, 1, 2], #[12, 1, 14, 9, 4, 11, 6, 7, 8, 3, 10, 5, 0, 13, 2], #[12, 13, 2, 9, 10, 5, 6, 7, 8, 3, 4, 11, 0, 1, 14], #[0, 4, 5, 3, 1, 2, 6, 13, 14, 9, 10, 11, 12, 7, 8], #[3, 1, 5, 0, 4, 2, 12, 7, 14, 9, 10, 11, 6, 13, 8], #[3, 4, 2, 0, 1, 5, 12, 13, 8, 9, 10, 11, 6, 7, 14], #[0, 10, 11, 3, 7, 8, 6, 4, 5, 9, 1, 2, 12, 13, 14], #[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2, 12, 13, 14], #[9, 10, 2, 6, 7, 5, 3, 4, 8, 0, 1, 11, 12, 13, 14]]
def sourceRow (i : Fin 15) (x : Fin 15) : Fin 15 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 15) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 15) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [2], [3], [0, 2], [3, 2], [1, 3], [4, 3], [3, 0, 2], [1, 3, 2], [4, 3, 2], [1, 1, 3], [1, 3, 0, 2], [4, 3, 0, 2], [1, 1, 3, 2], [1, 1, 3, 0, 2], [2, 0, 3, 1, 3, 4, 3, 0, 2], [2, 0, 3, 4, 4, 2, 1, 1, 3, 0, 2], [2, 0], [3, 0], [0, 2, 0], [3, 2, 0], [1, 3, 0], [4, 3, 0], [3, 0, 2, 0], [1, 3, 2, 0], [4, 3, 2, 0], [1, 1, 3, 0], [1, 3, 0, 2, 0], [4, 3, 0, 2, 0], [1, 1, 3, 2, 0], [1, 1, 3, 0, 2, 0], [1], [4], [2, 1], [3, 1], [4, 2], [3, 4], [2, 1, 1], [3, 1, 1], [0, 2, 1], [3, 2, 1], [1, 3, 1], [4, 3, 1], [4, 0, 2], [3, 4, 2], [3, 1, 3], [3, 4, 3], [1, 3, 4], [4, 3, 4], [0, 2, 1, 1], [3, 2, 1, 1], [1, 3, 1, 1], [3, 0, 2, 1], [1, 3, 2, 1], [4, 3, 2, 1], [3, 1, 3, 1], [3, 4, 0, 2], [3, 1, 3, 2], [3, 4, 3, 2], [1, 3, 4, 2], [4, 3, 4, 2], [1, 1, 3, 4], [3, 0, 2, 1, 1], [1, 3, 2, 1, 1], [1, 3, 0, 2, 1], [4, 3, 0, 2, 1], [3, 1, 3, 2, 1], [3, 1, 3, 0, 2], [3, 4, 3, 0, 2], [1, 3, 4, 0, 2], [4, 3, 4, 0, 2], [1, 1, 3, 4, 2], [1, 3, 0, 2, 1, 1], [3, 1, 3, 0, 2, 1], [1, 1, 3, 4, 0, 2], [1, 0], [4, 0], [1, 1, 0], [2, 1, 0], [3, 1, 0], [4, 2, 0], [3, 4, 0], [2, 1, 1, 0], [3, 1, 1, 0], [0, 2, 1, 0], [3, 2, 1, 0], [1, 3, 1, 0], [4, 3, 1, 0], [4, 0, 2, 0], [3, 4, 2, 0], [3, 1, 3, 0], [3, 4, 3, 0], [1, 3, 4, 0], [4, 3, 4, 0], [0, 2, 1, 1, 0], [3, 2, 1, 1, 0], [1, 3, 1, 1, 0], [3, 0, 2, 1, 0], [1, 3, 2, 1, 0], [4, 3, 2, 1, 0], [3, 1, 3, 1, 0], [3, 4, 0, 2, 0], [3, 1, 3, 2, 0], [3, 4, 3, 2, 0], [1, 3, 4, 2, 0], [4, 3, 4, 2, 0], [1, 1, 3, 4, 0], [3, 0, 2, 1, 1, 0], [1, 3, 2, 1, 1, 0], [1, 3, 0, 2, 1, 0], [4, 3, 0, 2, 1, 0], [3, 1, 3, 2, 1, 0], [3, 1, 3, 0, 2, 0], [3, 4, 3, 0, 2, 0], [1, 3, 4, 0, 2, 0], [4, 3, 4, 0, 2, 0], [1, 1, 3, 4, 2, 0], [1, 3, 0, 2, 1, 1, 0], [3, 1, 3, 0, 2, 1, 0], [1, 1, 3, 4, 0, 2, 0]]
def words (i : Fin 120) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 15 × Fin 15) := #[(0, 0), (0, 1), (0, 3), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 120)) := #[#[(0, 0), (1, 0), (1, 16), (2, 0), (3, 0), (3, 16), (2, 31), (3, 31), (3, 75), (2, 32), (3, 32), (3, 76), (2, 15), (3, 15), (3, 77)], #[(1, 1), (0, 1), (1, 17), (3, 1), (2, 1), (3, 17), (3, 33), (2, 33), (3, 78), (3, 35), (2, 35), (3, 80), (3, 37), (2, 37), (3, 82)], #[(1, 3), (1, 19), (0, 3), (3, 3), (3, 19), (2, 3), (3, 39), (3, 84), (2, 39), (3, 43), (3, 88), (2, 43), (3, 49), (3, 94), (2, 49)], #[(2, 2), (3, 2), (3, 18), (0, 2), (1, 2), (1, 18), (2, 38), (3, 38), (3, 83), (2, 36), (3, 36), (3, 81), (2, 34), (3, 34), (3, 79)], #[(3, 4), (2, 4), (3, 20), (1, 4), (0, 4), (1, 20), (3, 50), (2, 50), (3, 95), (3, 44), (2, 44), (3, 89), (3, 40), (2, 40), (3, 85)], #[(3, 7), (3, 23), (2, 7), (1, 7), (1, 23), (0, 7), (3, 62), (3, 107), (2, 62), (3, 56), (3, 101), (2, 56), (3, 52), (3, 97), (2, 52)], #[(2, 5), (3, 5), (3, 21), (2, 47), (3, 47), (3, 92), (0, 5), (1, 5), (1, 21), (2, 41), (3, 41), (3, 86), (2, 51), (3, 51), (3, 96)], #[(3, 8), (2, 8), (3, 24), (3, 59), (2, 59), (3, 104), (1, 8), (0, 8), (1, 24), (3, 53), (2, 53), (3, 98), (3, 63), (2, 63), (3, 108)], #[(3, 11), (3, 27), (2, 11), (3, 69), (3, 114), (2, 69), (1, 11), (1, 27), (0, 11), (3, 64), (3, 109), (2, 64), (3, 72), (3, 117), (2, 72)], #[(2, 6), (3, 6), (3, 22), (2, 46), (3, 46), (3, 91), (2, 42), (3, 42), (3, 87), (0, 6), (1, 6), (1, 22), (2, 48), (3, 48), (3, 93)], #[(3, 9), (2, 9), (3, 25), (3, 58), (2, 58), (3, 103), (3, 54), (2, 54), (3, 99), (1, 9), (0, 9), (1, 25), (3, 60), (2, 60), (3, 105)], #[(3, 12), (3, 28), (2, 12), (3, 68), (3, 113), (2, 68), (3, 65), (3, 110), (2, 65), (1, 12), (1, 28), (0, 12), (3, 70), (3, 115), (2, 70)], #[(2, 10), (3, 10), (3, 26), (2, 45), (3, 45), (3, 90), (2, 61), (3, 61), (3, 106), (2, 55), (3, 55), (3, 100), (0, 10), (1, 10), (1, 26)], #[(3, 13), (2, 13), (3, 29), (3, 57), (2, 57), (3, 102), (3, 71), (2, 71), (3, 116), (3, 66), (2, 66), (3, 111), (1, 13), (0, 13), (1, 29)], #[(3, 14), (3, 30), (2, 14), (3, 67), (3, 112), (2, 67), (3, 74), (3, 119), (2, 74), (3, 73), (3, 118), (2, 73), (1, 14), (1, 30), (0, 14)]]
def tr (x y : Fin 15) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![1, 3, 5, 15]
def valuesData : Array (Array (Fin 15)) := #[#[0], #[0, 1, 2], #[0, 3, 6, 9, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 15 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 120)) := #[#[15, 16], #[15, 0], #[16, 0], #[0, 0]]
def stabilizers (i : Fin 4) (j : Fin 2) : Fin 120 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 15) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 15) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 15)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target159 : ∀ p : Params, @Equation159 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1451 : ∀ p : Params, @Equation1451 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1657 : ∀ p : Params, @Equation1657 (Fin 15) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.Affine5Symmetric3

open Magma.Affine5Symmetric3

theorem Equation1451_not_structuralFromFin_Equation947_affine5Symmetric3 : ¬ Law1451.StructuralFromFin Law947 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law947.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1451 p ((@Law1451.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation1451_not_structuralFromFin_Equation947_affine5Symmetric3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1451_not_structuralFromFin_Equation947_affine5Symmetric3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1451._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1451_not_structuralFromFin_Equation947_affine5Symmetric3

theorem Equation159_not_structuralFromFin_Equation1370_affine5Symmetric3 : ¬ Law159.StructuralFromFin Law1370 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1370.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target159 p ((@Law159.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation159_not_structuralFromFin_Equation1370_affine5Symmetric3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation159_not_structuralFromFin_Equation1370_affine5Symmetric3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target159._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation159_not_structuralFromFin_Equation1370_affine5Symmetric3

theorem Equation1451_not_structuralFromFin_Equation1370_affine5Symmetric3 : ¬ Law1451.StructuralFromFin Law1370 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1370.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1451 p ((@Law1451.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation1451_not_structuralFromFin_Equation1370_affine5Symmetric3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1451_not_structuralFromFin_Equation1370_affine5Symmetric3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1451._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1451_not_structuralFromFin_Equation1370_affine5Symmetric3

theorem Equation1657_not_structuralFromFin_Equation1370_affine5Symmetric3 : ¬ Law1657.StructuralFromFin Law1370 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1370.models_iff (Fin 15) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1657 p ((@Law1657.models_iff (Fin 15) (fam p)).mp hp)

/-- info: 'Equation1657_not_structuralFromFin_Equation1370_affine5Symmetric3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1657_not_structuralFromFin_Equation1370_affine5Symmetric3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1657._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1657_not_structuralFromFin_Equation1370_affine5Symmetric3

