import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Ring3Degree2TruncatedPower1Witness16

def genData : Array (Array (Fin 9)) := #[#[1, 2, 0, 4, 5, 3, 7, 8, 6], #[3, 4, 5, 6, 7, 8, 0, 1, 2], #[0, 2, 1, 6, 8, 7, 3, 5, 4], #[0, 4, 8, 3, 7, 2, 6, 1, 5], #[0, 4, 5, 3, 7, 8, 6, 1, 2], #[2, 0, 1, 5, 3, 4, 8, 6, 7], #[6, 7, 8, 0, 1, 2, 3, 4, 5], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[0, 7, 8, 3, 1, 2, 6, 4, 5]]
def gen (i : Fin 9) (x : Fin 9) : Fin 9 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 9)) := #[#[2, 0, 1, 5, 3, 4, 8, 6, 7], #[6, 7, 8, 0, 1, 2, 3, 4, 5], #[0, 2, 1, 6, 8, 7, 3, 5, 4], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[0, 7, 8, 3, 1, 2, 6, 4, 5], #[1, 2, 0, 4, 5, 3, 7, 8, 6], #[3, 4, 5, 6, 7, 8, 0, 1, 2], #[0, 4, 8, 3, 7, 2, 6, 1, 5], #[0, 4, 5, 3, 7, 8, 6, 1, 2]]
def genInv (i : Fin 9) (x : Fin 9) : Fin 9 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 9)) := #[#[0, 2, 1, 3, 5, 4, 6, 8, 7]]
def probe (i : Fin 1) (x : Fin 9) : Fin 9 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 9)) := #[#[0, 2, 1, 3, 5, 4, 6, 8, 7]]
def probeInv (i : Fin 1) (x : Fin 9) : Fin 9 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 9)) := #[#[0, 7, 5, 3, 1, 8, 6, 4, 2], #[3, 1, 8, 6, 4, 2, 0, 7, 5], #[6, 4, 2, 0, 7, 5, 3, 1, 8], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[3, 1, 8, 6, 4, 2, 0, 7, 5], #[6, 4, 2, 0, 7, 5, 3, 1, 8], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[3, 1, 8, 6, 4, 2, 0, 7, 5], #[6, 4, 2, 0, 7, 5, 3, 1, 8]]
def sourceRow (i : Fin 9) (x : Fin 9) : Fin 9 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 9) : Equiv.Perm (Fin 9) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 9) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 9)) := #[[], [0], [1], [5], [6], [1, 0], [6, 0], [5, 1], [3, 5], [5, 1, 2, 5, 1], [3], [7], [2, 0], [3, 0], [7, 0], [2, 1], [3, 1], [7, 1], [0, 2], [1, 2], [3, 2], [4, 2], [0, 3], [5, 3], [6, 3], [4, 5], [6, 5], [7, 6], [0, 7], [5, 7], [2, 1, 0], [3, 1, 0], [1, 2, 0], [3, 2, 0], [7, 2, 0], [0, 3, 0], [7, 6, 0], [0, 7, 0], [0, 2, 1], [3, 2, 1], [4, 2, 1], [1, 0, 2], [3, 0, 2], [7, 0, 2], [3, 1, 2], [4, 1, 2], [0, 3, 2], [5, 3, 2], [0, 4, 2], [5, 4, 2], [3, 2, 1, 0], [7, 1, 2, 0], [5, 3, 2, 0], [5, 7, 2, 0], [2, 7, 5, 8, 5, 7, 2, 0], [2, 6, 8, 1, 2]]
def words (i : Fin 56) : List (Fin 9) := wordsData.getD i.val []
def repData : Array (Fin 9 × Fin 9) := #[(0, 0), (0, 1), (0, 3)]
def rep (i : Fin 3) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 3 × Fin 56)) := #[#[(0, 0), (1, 0), (1, 9), (2, 0), (1, 10), (1, 21), (2, 9), (1, 11), (1, 20)], #[(1, 18), (0, 1), (1, 1), (1, 48), (2, 1), (1, 22), (1, 46), (2, 18), (1, 28)], #[(1, 3), (1, 12), (0, 3), (1, 23), (1, 49), (2, 3), (1, 29), (1, 47), (2, 12)], #[(2, 19), (1, 17), (1, 44), (0, 2), (1, 2), (1, 19), (2, 2), (1, 16), (1, 45)], #[(1, 42), (2, 41), (1, 36), (1, 41), (0, 5), (1, 5), (1, 53), (2, 5), (1, 13)], #[(1, 25), (1, 50), (2, 32), (1, 7), (1, 32), (0, 7), (1, 35), (1, 34), (2, 7)], #[(2, 4), (1, 24), (1, 40), (2, 15), (1, 27), (1, 39), (0, 4), (1, 4), (1, 15)], #[(1, 43), (2, 6), (1, 31), (1, 52), (2, 38), (1, 14), (1, 38), (0, 6), (1, 6)], #[(1, 8), (1, 51), (2, 8), (1, 37), (1, 33), (2, 30), (1, 26), (1, 30), (0, 8)]]
def tr (x y : Fin 9) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 3 → ℕ := ![1, 6, 3]
def valuesData : Array (Array (Fin 9)) := #[#[0], #[0, 1, 3, 4, 6, 7], #[0, 3, 6]]
def values (i : Fin 3) (j : Fin (sizes i)) : Fin 9 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 56)) := #[#[9], #[54], #[55]]
def stabilizers (i : Fin 3) (j : Fin 1) : Fin 56 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 3) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 9) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 9) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 9)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target3724 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3724 (Fin 9) (fam p) := by native_decide

theorem target4283 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation4283 (Fin 9) (fam p) := by native_decide

end Magma.Ring3Degree2TruncatedPower1Witness16

open Magma.Ring3Degree2TruncatedPower1Witness16

theorem Equation3724_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16 : ¬ Law3724.StructuralFromFin Law727 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law727.models_iff (Fin 9) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3724 p hpattern ((@Law3724.models_iff (Fin 9) (fam p)).mp hp)

/-- info: 'Equation3724_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3724_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target3724._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3724_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16

theorem Equation4283_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16 : ¬ Law4283.StructuralFromFin Law727 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law727.models_iff (Fin 9) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4283 p hpattern ((@Law4283.models_iff (Fin 9) (fam p)).mp hp)

/-- info: 'Equation4283_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4283_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4283._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4283_not_structuralFromFin_Equation727_ring3Degree2TruncatedPower1Witness16

