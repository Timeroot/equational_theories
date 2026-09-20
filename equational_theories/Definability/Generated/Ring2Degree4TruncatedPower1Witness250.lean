import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Ring2Degree4TruncatedPower1Witness250

def genData : Array (Array (Fin 16)) := #[#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], #[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], #[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], #[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], #[0, 3, 6, 5, 12, 15, 10, 9, 8, 11, 14, 13, 4, 7, 2, 1], #[0, 7, 14, 9, 12, 11, 2, 5, 8, 15, 6, 1, 4, 3, 10, 13], #[0, 5, 2, 7, 4, 1, 6, 3, 8, 13, 10, 15, 12, 9, 14, 11], #[0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 5, 14, 7], #[0, 1, 10, 11, 4, 5, 14, 15, 8, 9, 2, 3, 12, 13, 6, 7], #[0, 15, 14, 1, 12, 3, 2, 13, 8, 7, 6, 9, 4, 11, 10, 5], #[0, 11, 6, 13, 12, 7, 10, 1, 8, 3, 14, 5, 4, 15, 2, 9]]
def gen (i : Fin 11) (x : Fin 16) : Fin 16 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 16)) := #[#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], #[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], #[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], #[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], #[0, 15, 14, 1, 12, 3, 2, 13, 8, 7, 6, 9, 4, 11, 10, 5], #[0, 11, 6, 13, 12, 7, 10, 1, 8, 3, 14, 5, 4, 15, 2, 9], #[0, 5, 2, 7, 4, 1, 6, 3, 8, 13, 10, 15, 12, 9, 14, 11], #[0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 5, 14, 7], #[0, 1, 10, 11, 4, 5, 14, 15, 8, 9, 2, 3, 12, 13, 6, 7], #[0, 3, 6, 5, 12, 15, 10, 9, 8, 11, 14, 13, 4, 7, 2, 1], #[0, 7, 14, 9, 12, 11, 2, 5, 8, 15, 6, 1, 4, 3, 10, 13]]
def genInv (i : Fin 11) (x : Fin 16) : Fin 16 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 16)) := #[#[0, 1, 6, 7, 4, 5, 2, 3, 8, 9, 14, 15, 12, 13, 10, 11], #[0, 3, 2, 1, 4, 7, 6, 5, 8, 11, 10, 9, 12, 15, 14, 13]]
def probe (i : Fin 2) (x : Fin 16) : Fin 16 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 16)) := #[#[0, 1, 6, 7, 4, 5, 2, 3, 8, 9, 14, 15, 12, 13, 10, 11], #[0, 3, 2, 1, 4, 7, 6, 5, 8, 11, 10, 9, 12, 15, 14, 13]]
def probeInv (i : Fin 2) (x : Fin 16) : Fin 16 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 16)) := #[#[0, 13, 14, 7, 0, 9, 2, 3, 0, 5, 6, 15, 0, 1, 10, 11], #[12, 1, 6, 15, 8, 1, 2, 3, 4, 1, 14, 7, 0, 1, 10, 11], #[12, 5, 2, 15, 0, 1, 2, 11, 4, 13, 2, 7, 8, 9, 2, 3], #[4, 13, 14, 3, 0, 1, 10, 3, 12, 5, 6, 3, 8, 9, 2, 3], #[4, 13, 6, 7, 4, 9, 10, 3, 4, 5, 14, 15, 4, 1, 2, 11], #[12, 5, 6, 7, 8, 5, 2, 11, 4, 5, 14, 15, 0, 5, 10, 3], #[4, 5, 6, 15, 8, 1, 6, 11, 12, 13, 6, 7, 0, 9, 6, 3], #[4, 5, 14, 7, 0, 9, 10, 7, 12, 13, 6, 7, 8, 1, 2, 7], #[8, 13, 14, 7, 8, 9, 2, 3, 8, 5, 6, 15, 8, 1, 10, 11], #[12, 9, 6, 15, 8, 9, 2, 3, 4, 9, 14, 7, 0, 9, 10, 11], #[12, 5, 10, 15, 0, 1, 10, 11, 4, 13, 10, 7, 8, 9, 10, 3], #[4, 13, 14, 11, 0, 1, 10, 11, 12, 5, 6, 11, 8, 9, 2, 11], #[12, 13, 6, 7, 12, 9, 10, 3, 12, 5, 14, 15, 12, 1, 2, 11], #[12, 13, 6, 7, 8, 13, 2, 11, 4, 13, 14, 15, 0, 13, 10, 3], #[4, 5, 14, 15, 8, 1, 14, 11, 12, 13, 14, 7, 0, 9, 14, 3], #[4, 5, 14, 15, 0, 9, 10, 15, 12, 13, 6, 15, 8, 1, 2, 15]]
def sourceRow (i : Fin 16) (x : Fin 16) : Fin 16 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 11) : Equiv.Perm (Fin 16) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 2) : Equiv.Perm (Fin 16) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 11)) := #[[], [0], [1], [2], [3], [1, 0], [2, 0], [3, 0], [5, 0], [9, 0], [10, 0], [2, 1], [3, 1], [5, 1], [3, 2], [10, 1, 0], [2, 5, 3, 2], [4], [6], [7], [9], [10], [4, 0], [6, 0], [7, 0], [4, 1], [6, 1], [7, 1], [9, 1], [10, 1], [4, 2], [5, 2], [6, 2], [7, 2], [9, 2], [10, 2], [4, 3], [5, 3], [6, 3], [7, 3], [9, 3], [10, 3], [0, 4], [1, 4], [2, 4], [10, 4], [0, 5], [1, 5], [2, 5], [0, 6], [0, 7], [0, 9], [1, 9], [2, 9], [0, 10], [1, 10], [2, 10], [2, 1, 0], [3, 1, 0], [4, 1, 0], [5, 1, 0], [6, 1, 0], [7, 1, 0], [3, 2, 0], [4, 2, 0], [5, 2, 0], [7, 2, 0], [9, 2, 0], [10, 2, 0], [4, 3, 0], [5, 3, 0], [6, 3, 0], [9, 3, 0], [10, 3, 0], [2, 4, 0], [10, 4, 0], [0, 5, 0], [1, 5, 0], [2, 5, 0], [1, 9, 0], [2, 9, 0], [0, 10, 0], [1, 10, 0], [2, 10, 0], [3, 2, 1], [4, 2, 1], [6, 2, 1], [7, 2, 1], [4, 3, 1], [6, 3, 1], [7, 3, 1], [9, 3, 1], [10, 3, 1], [10, 4, 1], [2, 5, 1], [0, 6, 1], [7, 6, 1], [0, 7, 1], [2, 9, 1], [6, 3, 2], [7, 3, 2], [0, 4, 2], [10, 4, 2], [0, 5, 2], [0, 7, 2], [0, 4, 3], [10, 4, 3], [0, 6, 3], [0, 9, 3], [5, 0, 4], [9, 0, 4], [10, 0, 4], [5, 1, 4], [10, 1, 4], [10, 2, 4], [0, 10, 4], [9, 0, 5], [5, 1, 5], [9, 1, 5], [7, 0, 6], [6, 0, 7], [2, 0, 9], [5, 0, 9], [6, 0, 9], [9, 0, 9], [4, 0, 10], [9, 0, 10], [10, 0, 10], [9, 0, 4, 6, 10, 0, 10], [8, 0], [8, 1], [8, 2], [8, 3], [1, 8], [8, 1, 0], [8, 2, 0], [8, 3, 0], [1, 8, 0], [8, 2, 1], [8, 3, 2], [1, 8, 2], [5, 0, 5]]
def words (i : Fin 142) : List (Fin 11) := wordsData.getD i.val []
def repData : Array (Fin 16 × Fin 16) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 8)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 142)) := #[#[(0, 0), (1, 0), (2, 0), (1, 17), (3, 0), (1, 18), (2, 17), (1, 16), (4, 0), (1, 19), (2, 128), (1, 21), (3, 17), (1, 45), (2, 16), (1, 20)], #[(1, 1), (0, 1), (1, 42), (2, 1), (1, 49), (3, 1), (1, 46), (2, 42), (1, 50), (4, 1), (1, 54), (2, 129), (1, 115), (3, 42), (1, 51), (2, 46)], #[(2, 2), (1, 43), (0, 2), (1, 2), (2, 43), (1, 47), (3, 2), (1, 26), (2, 133), (1, 55), (4, 2), (1, 27), (2, 47), (1, 52), (3, 43), (1, 96)], #[(1, 22), (2, 5), (1, 5), (0, 5), (1, 78), (2, 22), (1, 95), (3, 5), (1, 73), (2, 137), (1, 97), (4, 5), (1, 67), (2, 67), (1, 125), (3, 22)], #[(3, 3), (1, 32), (2, 44), (1, 48), (0, 3), (1, 3), (2, 3), (1, 44), (3, 44), (1, 102), (2, 48), (1, 53), (4, 3), (1, 33), (2, 131), (1, 56)], #[(1, 23), (3, 6), (1, 77), (2, 59), (1, 6), (0, 6), (1, 59), (2, 6), (1, 120), (3, 59), (1, 121), (2, 77), (1, 104), (4, 6), (1, 123), (2, 135)], #[(2, 25), (1, 76), (3, 11), (1, 86), (2, 11), (1, 25), (0, 11), (1, 11), (2, 76), (1, 91), (3, 25), (1, 113), (2, 140), (1, 29), (4, 11), (1, 87)], #[(1, 8), (2, 68), (1, 61), (3, 57), (1, 74), (2, 57), (1, 57), (0, 8), (1, 72), (2, 8), (1, 122), (3, 8), (1, 68), (2, 141), (1, 109), (4, 8)], #[(4, 4), (1, 39), (2, 132), (1, 41), (3, 36), (1, 106), (2, 37), (1, 40), (0, 4), (1, 4), (2, 4), (1, 36), (3, 4), (1, 38), (2, 36), (1, 37)], #[(1, 24), (4, 7), (1, 82), (2, 136), (1, 119), (3, 60), (1, 108), (2, 60), (1, 7), (0, 7), (1, 105), (2, 7), (1, 107), (3, 7), (1, 60), (2, 82)], #[(2, 130), (1, 81), (4, 12), (1, 90), (2, 94), (1, 98), (3, 81), (1, 93), (2, 12), (1, 85), (0, 12), (1, 12), (2, 81), (1, 94), (3, 12), (1, 89)], #[(1, 10), (2, 134), (1, 62), (4, 10), (1, 80), (2, 65), (1, 111), (3, 10), (1, 69), (2, 58), (1, 58), (0, 10), (1, 65), (2, 10), (1, 127), (3, 58)], #[(3, 30), (1, 114), (2, 31), (1, 34), (4, 14), (1, 100), (2, 139), (1, 35), (3, 14), (1, 99), (2, 30), (1, 31), (0, 14), (1, 14), (2, 14), (1, 30)], #[(1, 75), (3, 15), (1, 79), (2, 79), (1, 66), (4, 15), (1, 15), (2, 75), (1, 71), (3, 63), (1, 103), (2, 15), (1, 63), (0, 15), (1, 101), (2, 63)], #[(2, 13), (1, 28), (3, 13), (1, 118), (2, 138), (1, 92), (4, 13), (1, 112), (2, 88), (1, 13), (3, 84), (1, 117), (2, 84), (1, 88), (0, 13), (1, 84)], #[(1, 9), (2, 9), (1, 116), (3, 9), (1, 83), (2, 116), (1, 126), (4, 9), (1, 70), (2, 64), (1, 124), (3, 110), (1, 64), (2, 110), (1, 110), (0, 9)]]
def tr (x y : Fin 16) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![2, 8, 8, 4, 2]
def valuesData : Array (Array (Fin 16)) := #[#[0, 8], #[0, 1, 4, 5, 8, 9, 12, 13], #[0, 2, 4, 6, 8, 10, 12, 14], #[0, 4, 8, 12], #[0, 8]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 16 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 142)) := #[#[16], #[128], #[18], #[45], #[16]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 142 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 16) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 16) := ⟨sourceRow⟩
def pattern : Fin 2 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 16)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target4435 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation4435 (Fin 16) (fam p) := by native_decide

end Magma.Ring2Degree4TruncatedPower1Witness250

open Magma.Ring2Degree4TruncatedPower1Witness250

theorem Equation4435_not_structuralFromFin_Equation58_ring2Degree4TruncatedPower1Witness250 : ¬ Law4435.StructuralFromFin Law58 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law58.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation58_ring2Degree4TruncatedPower1Witness250' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4435_not_structuralFromFin_Equation58_ring2Degree4TruncatedPower1Witness250._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4435._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation58_ring2Degree4TruncatedPower1Witness250

theorem Equation4435_not_structuralFromFin_Equation446_ring2Degree4TruncatedPower1Witness250 : ¬ Law4435.StructuralFromFin Law446 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law446.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation446_ring2Degree4TruncatedPower1Witness250' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4435_not_structuralFromFin_Equation446_ring2Degree4TruncatedPower1Witness250._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4435._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation446_ring2Degree4TruncatedPower1Witness250

theorem Equation4435_not_structuralFromFin_Equation3728_ring2Degree4TruncatedPower1Witness250 : ¬ Law4435.StructuralFromFin Law3728 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3728.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4435 p hpattern ((@Law4435.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation4435_not_structuralFromFin_Equation3728_ring2Degree4TruncatedPower1Witness250' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4435_not_structuralFromFin_Equation3728_ring2Degree4TruncatedPower1Witness250._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4435._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4435_not_structuralFromFin_Equation3728_ring2Degree4TruncatedPower1Witness250

