import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.NonabelianAlternating4ConjugationPoint0Witness58

def genData : Array (Array (Fin 12)) := #[#[1, 2, 0, 6, 8, 7, 9, 11, 10, 3, 4, 5], #[3, 5, 4, 0, 2, 1, 10, 9, 11, 7, 6, 8], #[0, 1, 2, 8, 7, 6, 10, 9, 11, 4, 5, 3], #[0, 2, 1, 3, 5, 4, 9, 10, 11, 6, 7, 8], #[1, 2, 0, 5, 3, 4, 7, 8, 6, 11, 9, 10], #[2, 0, 1, 9, 10, 11, 3, 5, 4, 6, 8, 7], #[0, 1, 2, 11, 9, 10, 5, 4, 3, 7, 6, 8], #[2, 0, 1, 4, 5, 3, 8, 6, 7, 10, 11, 9]]
def gen (i : Fin 8) (x : Fin 12) : Fin 12 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 12)) := #[#[2, 0, 1, 9, 10, 11, 3, 5, 4, 6, 8, 7], #[3, 5, 4, 0, 2, 1, 10, 9, 11, 7, 6, 8], #[0, 1, 2, 11, 9, 10, 5, 4, 3, 7, 6, 8], #[0, 2, 1, 3, 5, 4, 9, 10, 11, 6, 7, 8], #[2, 0, 1, 4, 5, 3, 8, 6, 7, 10, 11, 9], #[1, 2, 0, 6, 8, 7, 9, 11, 10, 3, 4, 5], #[0, 1, 2, 8, 7, 6, 10, 9, 11, 4, 5, 3], #[1, 2, 0, 5, 3, 4, 7, 8, 6, 11, 9, 10]]
def genInv (i : Fin 8) (x : Fin 12) : Fin 12 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 12)) := #[#[3, 6, 9, 0, 7, 10, 1, 4, 11, 2, 5, 8]]
def probe (i : Fin 1) (x : Fin 12) : Fin 12 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 12)) := #[#[3, 6, 9, 0, 7, 10, 1, 4, 11, 2, 5, 8]]
def probeInv (i : Fin 1) (x : Fin 12) : Fin 12 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 12)) := #[#[0, 1, 2, 3, 9, 6, 10, 4, 8, 7, 5, 11], #[0, 1, 2, 11, 7, 5, 6, 9, 3, 4, 10, 8], #[0, 1, 2, 8, 4, 10, 5, 7, 11, 9, 6, 3], #[0, 10, 7, 3, 4, 5, 1, 9, 8, 2, 6, 11], #[11, 6, 2, 3, 4, 5, 10, 7, 0, 9, 1, 8], #[8, 1, 9, 3, 4, 5, 6, 2, 11, 7, 10, 0], #[11, 1, 4, 0, 9, 5, 6, 7, 8, 2, 10, 3], #[3, 10, 2, 11, 4, 1, 6, 7, 8, 9, 5, 0], #[0, 5, 9, 3, 2, 10, 6, 7, 8, 4, 1, 11], #[8, 5, 2, 0, 4, 6, 1, 7, 3, 9, 10, 11], #[3, 1, 7, 8, 2, 5, 6, 4, 0, 9, 10, 11], #[0, 6, 4, 3, 7, 1, 5, 2, 8, 9, 10, 11]]
def sourceRow (i : Fin 12) (x : Fin 12) : Fin 12 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 8) : Equiv.Perm (Fin 12) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 12) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 8)) := #[[], [0], [1], [5], [1, 0], [0, 1], [2, 1], [5, 1], [6, 1], [7, 1], [0, 1, 0], [6, 1, 0], [1, 6, 3, 6, 1], [5, 1, 3, 7, 1], [3, 0], [3, 1], [0, 3], [3, 1, 0], [3, 0, 1], [3, 2, 1], [0, 3, 1], [2, 3, 1], [4, 3, 1], [3, 0, 1, 0], [2, 3, 1, 0], [1, 3, 5, 7, 2, 3, 1, 0], [4], [6], [7], [2, 0], [4, 0], [4, 1], [1, 2], [1, 5], [1, 6], [2, 1, 0], [4, 1, 0], [5, 1, 0], [1, 2, 0], [1, 0, 1], [2, 0, 1], [4, 0, 1], [1, 2, 1], [1, 6, 1], [5, 1, 2], [0, 1, 5], [2, 1, 5], [6, 1, 5], [0, 1, 6], [2, 3], [4, 3], [7, 3], [3, 2, 0], [7, 3, 0], [7, 3, 1], [3, 1, 2], [1, 0, 3], [1, 2, 3], [3, 2, 1, 0], [0, 3, 1, 0], [7, 3, 1, 0], [3, 1, 2, 0], [3, 1, 0, 1], [3, 2, 0, 1], [7, 3, 0, 1], [3, 1, 2, 1], [1, 2, 3, 1], [0, 3, 1, 2], [2, 1, 0, 3], [5, 1, 0, 3], [6, 1, 0, 3], [5, 1, 2, 3]]
def words (i : Fin 72) : List (Fin 8) := wordsData.getD i.val []
def repData : Array (Fin 12 × Fin 12) := #[(0, 0), (0, 1), (0, 3), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 72)) := #[#[(0, 0), (1, 0), (1, 12), (2, 0), (3, 0), (3, 12), (3, 49), (3, 25), (2, 25), (3, 27), (3, 13), (2, 27)], #[(1, 16), (0, 1), (1, 1), (3, 26), (3, 50), (2, 26), (2, 1), (3, 16), (3, 1), (3, 53), (2, 29), (3, 29)], #[(1, 3), (1, 14), (0, 3), (3, 51), (2, 28), (3, 28), (3, 30), (2, 30), (3, 52), (2, 3), (3, 3), (3, 14)], #[(2, 2), (3, 15), (3, 2), (0, 2), (1, 15), (1, 2), (3, 55), (3, 34), (2, 34), (3, 32), (3, 57), (2, 32)], #[(3, 54), (3, 9), (2, 9), (1, 9), (0, 9), (1, 17), (3, 33), (2, 33), (3, 17), (2, 36), (3, 36), (3, 61)], #[(3, 31), (2, 31), (3, 22), (1, 22), (1, 4), (0, 4), (2, 38), (3, 60), (3, 38), (3, 56), (2, 4), (3, 4)], #[(3, 5), (2, 5), (3, 20), (3, 35), (3, 68), (2, 35), (0, 5), (1, 5), (1, 20), (3, 67), (2, 48), (3, 48)], #[(3, 63), (3, 41), (2, 41), (3, 62), (2, 10), (3, 10), (1, 24), (0, 10), (1, 10), (2, 46), (3, 46), (3, 24)], #[(2, 6), (3, 21), (3, 6), (2, 43), (3, 43), (3, 65), (1, 6), (1, 21), (0, 6), (3, 45), (3, 59), (2, 45)], #[(3, 18), (3, 7), (2, 7), (3, 58), (2, 47), (3, 47), (3, 44), (2, 44), (3, 71), (0, 7), (1, 18), (1, 7)], #[(3, 40), (2, 40), (3, 64), (3, 39), (3, 23), (2, 39), (2, 11), (3, 70), (3, 11), (1, 11), (0, 11), (1, 23)], #[(2, 8), (3, 19), (3, 8), (2, 42), (3, 42), (3, 66), (3, 69), (3, 37), (2, 37), (1, 19), (1, 8), (0, 8)]]
def tr (x y : Fin 12) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![1, 3, 2, 12]
def valuesData : Array (Array (Fin 12)) := #[#[0], #[0, 1, 2], #[0, 3], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 12 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 72)) := #[#[12, 13], #[25, 0], #[12, 0], #[0, 0]]
def stabilizers (i : Fin 4) (j : Fin 2) : Fin 72 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 12) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 12) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 12)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

private abbrev test3315 (p : Params) : Prop := ∀ y : Fin 12, ((fam p).op 0 y) = ((fam p).op 0 ((fam p).op y ((fam p).op 0 0)))
private theorem restricted3315 : ∀ p : Params, test3315 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target3315 : ∀ p : Params, @Equation3315 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted3315 p (ht 0)

private abbrev test4314 (p : Params) : Prop := ∀ y : Fin 12, ((fam p).op 0 ((fam p).op y 0)) = ((fam p).op 0 ((fam p).op y y))
private theorem restricted4314 : ∀ p : Params, test4314 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target4314 : ∀ p : Params, @Equation4314 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted4314 p (ht 0)

end Magma.NonabelianAlternating4ConjugationPoint0Witness58

open Magma.NonabelianAlternating4ConjugationPoint0Witness58

theorem Equation3315_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58 : ¬ Law3315.StructuralFromFin Law4406 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law4406.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3315 p ((@Law3315.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation3315_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3315_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted3315._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3315_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58

theorem Equation4314_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58 : ¬ Law4314.StructuralFromFin Law4406 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law4406.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target4314 p ((@Law4314.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation4314_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4314_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted4314._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4314_not_structuralFromFin_Equation4406_nonabelianAlternating4ConjugationPoint0Witness58

