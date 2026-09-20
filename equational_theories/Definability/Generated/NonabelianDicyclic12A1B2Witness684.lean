import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.NonabelianDicyclic12A1B2Witness684

def genData : Array (Array (Fin 12)) := #[#[1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6], #[6, 11, 10, 9, 8, 7, 3, 2, 1, 0, 5, 4], #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 6, 7], #[0, 5, 4, 3, 2, 1, 6, 11, 10, 9, 8, 7], #[1, 2, 3, 4, 5, 0, 11, 6, 7, 8, 9, 10], #[6, 7, 8, 9, 10, 11, 3, 4, 5, 0, 1, 2], #[0, 5, 4, 3, 2, 1, 6, 7, 8, 9, 10, 11], #[5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10], #[9, 8, 7, 6, 11, 10, 0, 5, 4, 3, 2, 1], #[0, 1, 2, 3, 4, 5, 10, 11, 6, 7, 8, 9], #[5, 0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 6], #[9, 10, 11, 6, 7, 8, 0, 1, 2, 3, 4, 5]]
def gen (i : Fin 12) (x : Fin 12) : Fin 12 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 12)) := #[#[5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10], #[9, 8, 7, 6, 11, 10, 0, 5, 4, 3, 2, 1], #[0, 1, 2, 3, 4, 5, 10, 11, 6, 7, 8, 9], #[0, 5, 4, 3, 2, 1, 6, 11, 10, 9, 8, 7], #[5, 0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 6], #[9, 10, 11, 6, 7, 8, 0, 1, 2, 3, 4, 5], #[0, 5, 4, 3, 2, 1, 6, 7, 8, 9, 10, 11], #[1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6], #[6, 11, 10, 9, 8, 7, 3, 2, 1, 0, 5, 4], #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 6, 7], #[1, 2, 3, 4, 5, 0, 11, 6, 7, 8, 9, 10], #[6, 7, 8, 9, 10, 11, 3, 4, 5, 0, 1, 2]]
def genInv (i : Fin 12) (x : Fin 12) : Fin 12 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 12)) := #[#[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 6]]
def probe (i : Fin 1) (x : Fin 12) : Fin 12 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 12)) := #[#[0, 1, 2, 3, 4, 5, 11, 6, 7, 8, 9, 10]]
def probeInv (i : Fin 1) (x : Fin 12) : Fin 12 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 12)) := #[#[0, 0, 3, 3, 3, 0, 0, 3, 0, 3, 0, 3], #[1, 1, 1, 4, 4, 4, 4, 1, 4, 1, 4, 1], #[5, 2, 2, 2, 5, 5, 2, 5, 2, 5, 2, 5], #[0, 0, 3, 3, 3, 0, 0, 3, 0, 3, 0, 3], #[1, 1, 1, 4, 4, 4, 4, 1, 4, 1, 4, 1], #[5, 2, 2, 2, 5, 5, 2, 5, 2, 5, 2, 5], #[9, 6, 9, 6, 9, 6, 6, 6, 9, 9, 9, 6], #[7, 10, 7, 10, 7, 10, 7, 7, 7, 10, 10, 10], #[11, 8, 11, 8, 11, 8, 11, 8, 8, 8, 11, 11], #[9, 6, 9, 6, 9, 6, 6, 6, 9, 9, 9, 6], #[7, 10, 7, 10, 7, 10, 7, 7, 7, 10, 10, 10], #[11, 8, 11, 8, 11, 8, 11, 8, 8, 8, 11, 11]]
def sourceRow (i : Fin 12) (x : Fin 12) : Fin 12 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 12) : Equiv.Perm (Fin 12) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 12) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 12)) := #[[], [0], [1], [7], [8], [0, 0], [1, 0], [5, 0], [8, 0], [11, 0], [1, 1], [7, 7], [7, 7, 6, 7, 7], [3], [5], [11], [3, 0], [0, 1], [5, 1], [9, 1], [0, 3], [2, 5], [4, 5], [3, 0, 0], [5, 1, 0], [3, 7, 10, 5, 1, 0], [2], [4], [10], [2, 0], [4, 0], [2, 1], [4, 1], [10, 1], [1, 2], [5, 2], [8, 2], [10, 2], [11, 2], [4, 4], [8, 4], [11, 4], [10, 7], [2, 8], [9, 8], [10, 10], [4, 0, 0], [4, 4, 0], [9, 5], [9, 8, 11, 4, 4, 0]]
def words (i : Fin 50) : List (Fin 12) := wordsData.getD i.val []
def repData : Array (Fin 12 × Fin 12) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 6), (0, 7)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 50)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (2, 13), (1, 13), (4, 0), (5, 0), (4, 26), (5, 26), (4, 25), (5, 13)], #[(1, 20), (0, 1), (1, 1), (2, 1), (3, 1), (2, 20), (5, 27), (4, 1), (5, 1), (4, 29), (5, 29), (4, 27)], #[(2, 24), (1, 24), (0, 5), (1, 5), (2, 5), (3, 5), (4, 30), (5, 30), (4, 5), (5, 5), (4, 39), (5, 39)], #[(3, 10), (2, 18), (1, 18), (0, 10), (1, 10), (2, 10), (5, 47), (4, 46), (5, 18), (4, 10), (5, 10), (4, 47)], #[(2, 11), (3, 11), (2, 23), (1, 23), (0, 11), (1, 11), (4, 42), (5, 42), (4, 45), (5, 45), (4, 11), (5, 11)], #[(1, 3), (2, 3), (3, 3), (2, 16), (1, 16), (0, 3), (5, 3), (4, 28), (5, 28), (4, 37), (5, 16), (4, 3)], #[(5, 34), (4, 34), (5, 2), (4, 2), (5, 14), (4, 35), (0, 2), (1, 14), (2, 14), (3, 2), (2, 2), (1, 2)], #[(4, 44), (5, 33), (4, 33), (5, 17), (4, 7), (5, 7), (1, 17), (0, 7), (1, 7), (2, 7), (3, 7), (2, 17)], #[(5, 40), (4, 40), (5, 31), (4, 31), (5, 8), (4, 8), (2, 8), (1, 8), (0, 8), (1, 21), (2, 21), (3, 8)], #[(4, 4), (5, 15), (4, 38), (5, 36), (4, 36), (5, 4), (3, 4), (2, 4), (1, 4), (0, 4), (1, 15), (2, 15)], #[(5, 41), (4, 9), (5, 9), (4, 19), (5, 48), (4, 41), (2, 9), (3, 9), (2, 19), (1, 19), (0, 9), (1, 9)], #[(4, 43), (5, 6), (4, 6), (5, 32), (4, 32), (5, 22), (1, 22), (2, 22), (3, 6), (2, 6), (1, 6), (0, 6)]]
def tr (x y : Fin 12) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![2, 6, 6, 2, 4, 4]
def valuesData : Array (Array (Fin 12)) := #[#[0, 3], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 3], #[0, 3, 6, 9], #[0, 3, 7, 10]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 12 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 50)) := #[#[12], #[25], #[25], #[12], #[13], #[49]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 50 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 12) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 12) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 12)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target105 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation105 (Fin 12) (fam p) := by native_decide

theorem target1239 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1239 (Fin 12) (fam p) := by native_decide

theorem target3462 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3462 (Fin 12) (fam p) := by native_decide

end Magma.NonabelianDicyclic12A1B2Witness684

open Magma.NonabelianDicyclic12A1B2Witness684

theorem Equation105_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684 : ¬ Law105.StructuralFromFin Law4402 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law4402.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target105 p hpattern ((@Law105.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation105_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation105_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target105._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation105_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684

theorem Equation1239_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684 : ¬ Law1239.StructuralFromFin Law4402 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law4402.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1239 p hpattern ((@Law1239.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation1239_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1239_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target1239._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1239_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684

theorem Equation3462_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684 : ¬ Law3462.StructuralFromFin Law4402 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law4402.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3462 p hpattern ((@Law3462.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation3462_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3462_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target3462._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3462_not_structuralFromFin_Equation4402_nonabelianDicyclic12A1B2Witness684

