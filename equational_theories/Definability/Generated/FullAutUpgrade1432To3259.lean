import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.FullAutUpgrade1432To3259

def genData : Array (Array (Fin 8)) := #[#[0, 3, 6, 1, 4, 7, 2, 5], #[1, 2, 3, 4, 5, 6, 7, 0], #[7, 0, 1, 2, 3, 4, 5, 6]]
def gen (i : Fin 3) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[0, 3, 6, 1, 4, 7, 2, 5], #[7, 0, 1, 2, 3, 4, 5, 6], #[1, 2, 3, 4, 5, 6, 7, 0]]
def genInv (i : Fin 3) (x : Fin 8) : Fin 8 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 8)) := #[#[0, 2, 1, 7, 4, 6, 5, 3], #[0, 2, 7, 5, 4, 6, 3, 1]]
def probe (i : Fin 2) (x : Fin 8) : Fin 8 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 8)) := #[#[0, 2, 1, 7, 4, 6, 5, 3], #[0, 7, 1, 6, 4, 3, 5, 2]]
def probeInv (i : Fin 2) (x : Fin 8) : Fin 8 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 8)) := #[#[4, 4, 7, 4, 4, 2, 5, 6], #[7, 5, 5, 0, 5, 5, 3, 6], #[7, 0, 6, 6, 1, 6, 6, 4], #[5, 0, 1, 7, 7, 2, 7, 7], #[0, 6, 1, 2, 0, 0, 3, 0], #[1, 1, 7, 2, 3, 1, 1, 4], #[5, 2, 2, 0, 3, 4, 2, 2], #[3, 6, 3, 3, 1, 4, 5, 3]]
def sourceRow (i : Fin 8) (x : Fin 8) : Fin 8 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 3) : Equiv.Perm (Fin 8) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 2) : Equiv.Perm (Fin 8) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 3)) := #[[], [1], [2], [0, 1], [1, 1], [0, 2], [2, 2], [1, 0, 1], [2, 0, 2, 0, 1, 0, 1], [1, 0], [2, 0], [0, 1, 0], [1, 1, 0], [0, 2, 0], [2, 2, 0], [1, 0, 1, 0]]
def words (i : Fin 16) : List (Fin 3) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 5)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 16)) := #[#[(0, 0), (1, 0), (2, 0), (1, 8), (3, 0), (4, 0), (2, 8), (4, 8)], #[(4, 9), (0, 1), (1, 1), (2, 1), (1, 9), (3, 1), (4, 1), (2, 9)], #[(2, 12), (4, 12), (0, 4), (1, 4), (2, 4), (1, 12), (3, 4), (4, 4)], #[(4, 11), (2, 3), (4, 3), (0, 3), (1, 11), (2, 11), (1, 3), (3, 3)], #[(3, 7), (4, 15), (2, 7), (4, 7), (0, 7), (1, 15), (2, 15), (1, 7)], #[(1, 5), (3, 5), (4, 13), (2, 5), (4, 5), (0, 5), (1, 13), (2, 13)], #[(2, 6), (1, 14), (3, 6), (4, 6), (2, 14), (4, 14), (0, 6), (1, 6)], #[(1, 2), (2, 2), (1, 10), (3, 2), (4, 2), (2, 10), (4, 10), (0, 2)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![2, 8, 8, 2, 8]
def valuesData : Array (Array (Fin 8)) := #[#[0, 4], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 4], #[0, 1, 2, 3, 4, 5, 6, 7]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 16)) := #[#[8], #[0], #[0], #[8], #[0]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 16 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 8) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 8) := ⟨sourceRow⟩
def pattern : Fin 2 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 8)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

private abbrev test3259 (p : Params) : Prop := ∀ y : Fin 8, ((fam p).op 0 0) = ((fam p).op 0 ((fam p).op y ((fam p).op 0 y)))
private theorem restricted3259 : ∀ p : Params, test3259 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target3259 : ∀ p : Params, @Equation3259 (Fin 8) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted3259 p (ht 0)

end Magma.FullAutUpgrade1432To3259

open Magma.FullAutUpgrade1432To3259

theorem Equation3259_not_structuralFromFin_Equation1432_fullAutUpgrade1432To3259 : ¬ Law3259.StructuralFromFin Law1432 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1432.models_iff (Fin 8) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3259 p ((@Law3259.models_iff (Fin 8) (fam p)).mp hp)

/-- info: 'Equation3259_not_structuralFromFin_Equation1432_fullAutUpgrade1432To3259' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3259_not_structuralFromFin_Equation1432_fullAutUpgrade1432To3259._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted3259._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3259_not_structuralFromFin_Equation1432_fullAutUpgrade1432To3259

