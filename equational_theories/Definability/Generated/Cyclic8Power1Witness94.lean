import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Cyclic8Power1Witness94

def genData : Array (Array (Fin 8)) := #[#[1, 2, 3, 4, 5, 6, 7, 0], #[0, 3, 6, 1, 4, 7, 2, 5], #[0, 5, 2, 7, 4, 1, 6, 3], #[4, 1, 6, 3, 0, 5, 2, 7], #[7, 0, 1, 2, 3, 4, 5, 6]]
def gen (i : Fin 5) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[7, 0, 1, 2, 3, 4, 5, 6], #[0, 3, 6, 1, 4, 7, 2, 5], #[0, 5, 2, 7, 4, 1, 6, 3], #[4, 1, 6, 3, 0, 5, 2, 7], #[1, 2, 3, 4, 5, 6, 7, 0]]
def genInv (i : Fin 5) (x : Fin 8) : Fin 8 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 8)) := #[#[4, 1, 2, 3, 0, 5, 6, 7]]
def probe (i : Fin 1) (x : Fin 8) : Fin 8 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 8)) := #[#[4, 1, 2, 3, 0, 5, 6, 7]]
def probeInv (i : Fin 1) (x : Fin 8) : Fin 8 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 8)) := #[#[0, 7, 2, 5, 4, 3, 6, 1], #[2, 1, 0, 3, 6, 5, 4, 7], #[0, 3, 2, 1, 4, 7, 6, 5], #[6, 1, 4, 3, 2, 5, 0, 7], #[0, 7, 2, 5, 4, 3, 6, 1], #[2, 1, 0, 3, 6, 5, 4, 7], #[0, 3, 2, 1, 4, 7, 6, 5], #[6, 1, 4, 3, 2, 5, 0, 7]]
def sourceRow (i : Fin 8) (x : Fin 8) : Fin 8 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 8) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 8) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [0], [3], [4], [0, 0], [1, 0], [2, 0], [4, 4], [0, 1, 2, 0], [1], [2], [3, 0], [0, 1], [3, 1], [4, 1], [3, 2], [4, 2], [4, 3], [1, 4], [0, 0, 0], [1, 0, 0], [2, 0, 0], [3, 0, 0], [0, 1, 0], [2, 1, 0], [3, 1, 0], [4, 1, 0], [3, 2, 0], [2, 0, 1], [3, 0, 1], [2, 1, 0, 0], [3, 1, 0, 0]]
def words (i : Fin 32) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 2), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 32)) := #[#[(0, 0), (1, 0), (2, 0), (1, 9), (3, 0), (1, 10), (2, 9), (1, 8)], #[(1, 29), (0, 1), (1, 1), (2, 1), (1, 12), (3, 1), (1, 11), (2, 12)], #[(2, 26), (1, 31), (0, 4), (1, 4), (2, 4), (1, 26), (3, 4), (1, 21)], #[(1, 17), (2, 5), (1, 25), (0, 5), (1, 19), (2, 17), (1, 5), (3, 5)], #[(3, 2), (1, 2), (2, 13), (1, 13), (0, 2), (1, 15), (2, 2), (1, 23)], #[(1, 18), (3, 6), (1, 6), (2, 18), (1, 28), (0, 6), (1, 27), (2, 6)], #[(2, 7), (1, 20), (3, 7), (1, 22), (2, 20), (1, 30), (0, 7), (1, 7)], #[(1, 3), (2, 3), (1, 14), (3, 3), (1, 16), (2, 14), (1, 24), (0, 3)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![2, 8, 4, 2]
def valuesData : Array (Array (Fin 8)) := #[#[0, 4], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 4, 6], #[0, 4]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 32)) := #[#[8], #[0], #[10], #[8]]
def stabilizers (i : Fin 4) (j : Fin 1) : Fin 32 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 8) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 8) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 8)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target1278 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1278 (Fin 8) (fam p) := by native_decide

theorem target3315 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3315 (Fin 8) (fam p) := by native_decide

end Magma.Cyclic8Power1Witness94

open Magma.Cyclic8Power1Witness94

theorem Equation1278_not_structuralFromFin_Equation3388_cyclic8Power1Witness94 : ¬ Law1278.StructuralFromFin Law3388 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3388.models_iff (Fin 8) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1278 p hpattern ((@Law1278.models_iff (Fin 8) (fam p)).mp hp)

/-- info: 'Equation1278_not_structuralFromFin_Equation3388_cyclic8Power1Witness94' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1278_not_structuralFromFin_Equation3388_cyclic8Power1Witness94._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target1278._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1278_not_structuralFromFin_Equation3388_cyclic8Power1Witness94

theorem Equation3315_not_structuralFromFin_Equation3388_cyclic8Power1Witness94 : ¬ Law3315.StructuralFromFin Law3388 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3388.models_iff (Fin 8) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3315 p hpattern ((@Law3315.models_iff (Fin 8) (fam p)).mp hp)

/-- info: 'Equation3315_not_structuralFromFin_Equation3388_cyclic8Power1Witness94' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3315_not_structuralFromFin_Equation3388_cyclic8Power1Witness94._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target3315._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3315_not_structuralFromFin_Equation3388_cyclic8Power1Witness94

