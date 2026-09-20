import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Cyclic18Power1Witness38579

def genData : Array (Array (Fin 18)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0], #[0, 5, 10, 15, 2, 7, 12, 17, 4, 9, 14, 1, 6, 11, 16, 3, 8, 13], #[17, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], #[0, 11, 4, 15, 8, 1, 12, 5, 16, 9, 2, 13, 6, 17, 10, 3, 14, 7]]
def gen (i : Fin 4) (x : Fin 18) : Fin 18 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 18)) := #[#[17, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], #[0, 11, 4, 15, 8, 1, 12, 5, 16, 9, 2, 13, 6, 17, 10, 3, 14, 7], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0], #[0, 5, 10, 15, 2, 7, 12, 17, 4, 9, 14, 1, 6, 11, 16, 3, 8, 13]]
def genInv (i : Fin 4) (x : Fin 18) : Fin 18 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 18)) := #[#[0, 7, 8, 3, 10, 11, 6, 13, 14, 9, 16, 17, 12, 1, 2, 15, 4, 5]]
def probe (i : Fin 1) (x : Fin 18) : Fin 18 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 18)) := #[#[0, 13, 14, 3, 16, 17, 6, 1, 2, 9, 4, 5, 12, 7, 8, 15, 10, 11]]
def probeInv (i : Fin 1) (x : Fin 18) : Fin 18 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 18)) := #[#[9, 11, 9, 15, 9, 1, 9, 5, 9, 9, 9, 13, 9, 17, 9, 3, 9, 7], #[8, 10, 12, 10, 16, 10, 2, 10, 6, 10, 10, 10, 14, 10, 0, 10, 4, 10], #[11, 9, 11, 13, 11, 17, 11, 3, 11, 7, 11, 11, 11, 15, 11, 1, 11, 5], #[6, 12, 10, 12, 14, 12, 0, 12, 4, 12, 8, 12, 12, 12, 16, 12, 2, 12], #[13, 7, 13, 11, 13, 15, 13, 1, 13, 5, 13, 9, 13, 13, 13, 17, 13, 3], #[4, 14, 8, 14, 12, 14, 16, 14, 2, 14, 6, 14, 10, 14, 14, 14, 0, 14], #[15, 5, 15, 9, 15, 13, 15, 17, 15, 3, 15, 7, 15, 11, 15, 15, 15, 1], #[2, 16, 6, 16, 10, 16, 14, 16, 0, 16, 4, 16, 8, 16, 12, 16, 16, 16], #[17, 3, 17, 7, 17, 11, 17, 15, 17, 1, 17, 5, 17, 9, 17, 13, 17, 17], #[0, 0, 4, 0, 8, 0, 12, 0, 16, 0, 2, 0, 6, 0, 10, 0, 14, 0], #[1, 1, 1, 5, 1, 9, 1, 13, 1, 17, 1, 3, 1, 7, 1, 11, 1, 15], #[16, 2, 2, 2, 6, 2, 10, 2, 14, 2, 0, 2, 4, 2, 8, 2, 12, 2], #[3, 17, 3, 3, 3, 7, 3, 11, 3, 15, 3, 1, 3, 5, 3, 9, 3, 13], #[14, 4, 0, 4, 4, 4, 8, 4, 12, 4, 16, 4, 2, 4, 6, 4, 10, 4], #[5, 15, 5, 1, 5, 5, 5, 9, 5, 13, 5, 17, 5, 3, 5, 7, 5, 11], #[12, 6, 16, 6, 2, 6, 6, 6, 10, 6, 14, 6, 0, 6, 4, 6, 8, 6], #[7, 13, 7, 17, 7, 3, 7, 7, 7, 11, 7, 15, 7, 1, 7, 5, 7, 9], #[10, 8, 14, 8, 0, 8, 4, 8, 8, 8, 12, 8, 16, 8, 2, 8, 6, 8]]
def sourceRow (i : Fin 18) (x : Fin 18) : Fin 18 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 18) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 18) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [1, 0], [3, 0], [1, 2], [2, 2], [3, 2], [0, 0, 0], [1, 0, 0], [3, 0, 0], [0, 1, 0], [0, 3, 0], [0, 1, 2], [1, 2, 2], [2, 2, 2], [2, 1, 0, 0], [2, 2, 1, 1, 1, 2, 2], [1], [3], [0, 1], [1, 1], [2, 1], [0, 3], [2, 3], [3, 3], [1, 1, 0], [2, 1, 0], [2, 3, 0], [3, 3, 0], [0, 0, 1], [1, 0, 1], [3, 0, 1], [0, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [3, 2, 1], [1, 1, 2], [2, 1, 2], [3, 2, 2], [0, 3, 2], [2, 3, 2], [3, 3, 2], [0, 0, 3], [1, 0, 3], [3, 0, 3], [1, 2, 3], [2, 2, 3], [3, 2, 3], [0, 3, 3], [2, 3, 3], [0, 0, 0, 0], [1, 0, 0, 0], [3, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [0, 3, 0, 0], [2, 3, 0, 0], [3, 3, 0, 0], [0, 0, 1, 0], [1, 0, 1, 0], [3, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [2, 1, 1, 0], [1, 2, 1, 0], [2, 2, 1, 0], [3, 2, 1, 0], [0, 0, 3, 0], [1, 0, 3, 0], [3, 0, 3, 0], [1, 2, 3, 0], [2, 2, 3, 0], [3, 2, 3, 0], [0, 3, 3, 0], [2, 3, 3, 0], [1, 0, 0, 1], [1, 1, 0, 1], [2, 1, 0, 1], [2, 3, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 2, 1, 1], [2, 2, 1, 1], [1, 1, 2, 1], [3, 3, 2, 2], [3, 0, 3, 2], [2, 3, 3, 2], [1, 1, 0, 0, 0], [3, 3, 0, 0, 0], [0, 1, 1, 0, 0], [1, 1, 1, 0, 0], [1, 2, 1, 0, 0], [3, 2, 1, 0, 0], [3, 2, 3, 0, 0], [0, 3, 3, 0, 0], [1, 1, 0, 1, 0], [1, 0, 1, 1, 0], [1, 2, 1, 1, 0], [1, 1, 2, 1, 0], [1, 1, 0, 0, 1], [0, 1, 1, 0, 1], [1, 2, 1, 0, 1], [1, 1, 1, 0, 0, 0], [1, 0, 1, 1, 0, 0], [1, 1, 2, 1, 0, 0]]
def words (i : Fin 108) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 18 × Fin 18) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 6), (0, 9)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 108)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (2, 20), (1, 19), (4, 0), (1, 22), (2, 26), (5, 0), (2, 19), (1, 20), (4, 19), (1, 26), (2, 22), (3, 19), (2, 18), (1, 18)], #[(1, 83), (0, 1), (1, 1), (2, 1), (3, 1), (2, 24), (1, 21), (4, 1), (1, 34), (2, 51), (5, 1), (2, 21), (1, 24), (4, 21), (1, 51), (2, 34), (3, 21), (2, 83)], #[(2, 104), (1, 104), (0, 3), (1, 3), (2, 3), (3, 3), (2, 45), (1, 31), (4, 3), (1, 67), (2, 75), (5, 3), (2, 31), (1, 45), (4, 31), (1, 75), (2, 67), (3, 31)], #[(3, 59), (2, 106), (1, 106), (0, 9), (1, 9), (2, 9), (3, 9), (2, 59), (1, 68), (4, 9), (1, 90), (2, 91), (5, 9), (2, 68), (1, 59), (4, 59), (1, 91), (2, 90)], #[(2, 80), (3, 11), (2, 99), (1, 99), (0, 11), (1, 53), (2, 53), (3, 53), (2, 11), (1, 28), (4, 53), (1, 80), (2, 89), (5, 11), (2, 28), (1, 11), (4, 11), (1, 89)], #[(1, 44), (2, 32), (3, 4), (2, 82), (1, 82), (0, 4), (1, 46), (2, 46), (3, 32), (2, 58), (1, 4), (4, 32), (1, 32), (2, 44), (5, 4), (2, 4), (1, 58), (4, 4)], #[(4, 12), (1, 72), (2, 66), (3, 12), (2, 98), (1, 98), (0, 12), (1, 71), (2, 71), (3, 66), (2, 43), (1, 12), (4, 66), (1, 66), (2, 72), (5, 12), (2, 12), (1, 43)], #[(1, 8), (4, 8), (1, 50), (2, 27), (3, 8), (2, 79), (1, 79), (0, 8), (1, 38), (2, 38), (3, 27), (2, 8), (1, 61), (4, 27), (1, 27), (2, 50), (5, 8), (2, 61)], #[(2, 15), (1, 42), (4, 15), (1, 60), (2, 64), (3, 15), (2, 103), (1, 103), (0, 15), (1, 69), (2, 69), (3, 60), (2, 42), (1, 15), (4, 60), (1, 64), (2, 60), (5, 15)], #[(5, 17), (2, 17), (1, 74), (4, 17), (1, 97), (2, 94), (3, 17), (2, 107), (1, 107), (0, 17), (1, 95), (2, 95), (3, 94), (2, 74), (1, 17), (4, 94), (1, 94), (2, 97)], #[(2, 87), (5, 10), (2, 10), (1, 29), (4, 10), (1, 87), (2, 78), (3, 10), (2, 101), (1, 101), (0, 10), (1, 81), (2, 81), (3, 78), (2, 29), (1, 10), (4, 78), (1, 78)], #[(1, 39), (2, 47), (5, 5), (2, 56), (1, 5), (4, 5), (1, 47), (2, 39), (3, 5), (2, 86), (1, 86), (0, 5), (1, 33), (2, 33), (3, 33), (2, 5), (1, 56), (4, 33)], #[(4, 62), (1, 62), (2, 77), (5, 13), (2, 40), (1, 13), (4, 13), (1, 77), (2, 62), (3, 13), (2, 100), (1, 100), (0, 13), (1, 63), (2, 63), (3, 62), (2, 13), (1, 40)], #[(1, 6), (4, 30), (1, 36), (2, 30), (5, 6), (2, 6), (1, 70), (4, 6), (1, 30), (2, 36), (3, 6), (2, 84), (1, 84), (0, 6), (1, 48), (2, 48), (3, 30), (2, 70)], #[(2, 41), (1, 14), (4, 57), (1, 57), (2, 76), (5, 14), (2, 14), (1, 41), (4, 14), (1, 76), (2, 57), (3, 14), (2, 102), (1, 102), (0, 14), (1, 73), (2, 73), (3, 57)], #[(3, 16), (2, 55), (1, 54), (4, 16), (1, 92), (2, 96), (5, 16), (2, 54), (1, 55), (4, 54), (1, 96), (2, 92), (3, 54), (2, 105), (1, 105), (0, 16), (1, 16), (2, 16)], #[(2, 7), (3, 7), (2, 49), (1, 37), (4, 7), (1, 85), (2, 88), (5, 7), (2, 37), (1, 49), (4, 37), (1, 88), (2, 85), (3, 37), (2, 93), (1, 93), (0, 7), (1, 7)], #[(1, 2), (2, 2), (3, 2), (2, 25), (1, 23), (4, 2), (1, 35), (2, 52), (5, 2), (2, 23), (1, 25), (4, 23), (1, 52), (2, 35), (3, 23), (2, 65), (1, 65), (0, 2)]]
def tr (x y : Fin 18) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![2, 18, 18, 6, 6, 2]
def valuesData : Array (Array (Fin 18)) := #[#[0, 9], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 3, 6, 9, 12, 15], #[0, 3, 6, 9, 12, 15], #[0, 9]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 18 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 108)) := #[#[18], #[0], #[0], #[26], #[26], #[18]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 108 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 18) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 18) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 18)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target159 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation159 (Fin 18) (fam p) := by native_decide

theorem target3667 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3667 (Fin 18) (fam p) := by native_decide

end Magma.Cyclic18Power1Witness38579

open Magma.Cyclic18Power1Witness38579

theorem Equation159_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579 : ¬ Law159.StructuralFromFin Law1453 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1453.models_iff (Fin 18) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target159 p hpattern ((@Law159.models_iff (Fin 18) (fam p)).mp hp)

/-- info: 'Equation159_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation159_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target159._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation159_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579

theorem Equation3667_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579 : ¬ Law3667.StructuralFromFin Law1453 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1453.models_iff (Fin 18) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3667 p hpattern ((@Law3667.models_iff (Fin 18) (fam p)).mp hp)

/-- info: 'Equation3667_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3667_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target3667._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3667_not_structuralFromFin_Equation1453_cyclic18Power1Witness38579

