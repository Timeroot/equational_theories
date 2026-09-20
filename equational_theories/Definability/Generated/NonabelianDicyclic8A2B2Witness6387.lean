import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.NonabelianDicyclic8A2B2Witness6387

def genData : Array (Array (Fin 8)) := #[#[1, 2, 3, 0, 5, 6, 7, 4], #[4, 7, 6, 5, 2, 1, 0, 3], #[0, 1, 2, 3, 6, 7, 4, 5], #[1, 2, 3, 0, 7, 4, 5, 6], #[3, 0, 1, 2, 7, 4, 5, 6], #[6, 5, 4, 7, 0, 3, 2, 1], #[3, 0, 1, 2, 5, 6, 7, 4]]
def gen (i : Fin 7) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[3, 0, 1, 2, 7, 4, 5, 6], #[6, 5, 4, 7, 0, 3, 2, 1], #[0, 1, 2, 3, 6, 7, 4, 5], #[3, 0, 1, 2, 5, 6, 7, 4], #[1, 2, 3, 0, 5, 6, 7, 4], #[4, 7, 6, 5, 2, 1, 0, 3], #[1, 2, 3, 0, 7, 4, 5, 6]]
def genInv (i : Fin 7) (x : Fin 8) : Fin 8 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 8)) := #[#[0, 1, 2, 3, 5, 6, 7, 4]]
def probe (i : Fin 1) (x : Fin 8) : Fin 8 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 8)) := #[#[0, 1, 2, 3, 7, 4, 5, 6]]
def probeInv (i : Fin 1) (x : Fin 8) : Fin 8 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 8)) := #[#[3, 0, 3, 3, 0, 3, 0, 3], #[0, 0, 1, 0, 0, 1, 0, 1], #[1, 1, 1, 2, 2, 1, 2, 1], #[3, 2, 2, 2, 2, 3, 2, 3], #[4, 5, 4, 5, 5, 5, 5, 4], #[6, 5, 6, 5, 5, 6, 6, 6], #[6, 7, 6, 7, 7, 6, 7, 7], #[4, 7, 4, 7, 4, 4, 7, 4]]
def sourceRow (i : Fin 8) (x : Fin 8) : Fin 8 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 7) : Equiv.Perm (Fin 8) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 8) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 7)) := #[[], [0], [1], [4], [5], [0, 0], [1, 0], [5, 0], [1, 6, 5, 0], [3], [6], [3, 0], [2, 1], [3, 1], [6, 1], [1, 2]]
def words (i : Fin 16) : List (Fin 7) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 16)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (4, 8), (5, 8)], #[(3, 1), (0, 1), (1, 1), (2, 1), (5, 9), (4, 1), (5, 1), (4, 9)], #[(2, 5), (3, 5), (0, 5), (1, 5), (4, 11), (5, 11), (4, 5), (5, 5)], #[(1, 3), (2, 3), (3, 3), (0, 3), (5, 3), (4, 10), (5, 10), (4, 3)], #[(4, 15), (5, 2), (4, 2), (5, 15), (0, 2), (3, 2), (2, 2), (1, 2)], #[(5, 14), (4, 14), (5, 7), (4, 7), (1, 7), (0, 7), (3, 7), (2, 7)], #[(4, 4), (5, 12), (4, 12), (5, 4), (2, 4), (1, 4), (0, 4), (3, 4)], #[(5, 6), (4, 6), (5, 13), (4, 13), (3, 6), (2, 6), (1, 6), (0, 6)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![4, 4, 4, 4, 8, 8]
def valuesData : Array (Array (Fin 8)) := #[#[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 16)) := #[#[8], #[8], #[8], #[8], #[0], #[0]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 16 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 8) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 8) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 8)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target4406 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation4406 (Fin 8) (fam p) := by native_decide

end Magma.NonabelianDicyclic8A2B2Witness6387

open Magma.NonabelianDicyclic8A2B2Witness6387

theorem Equation4406_not_structuralFromFin_Equation4401_nonabelianDicyclic8A2B2Witness6387 : ¬ Law4406.StructuralFromFin Law4401 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law4401.models_iff (Fin 8) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4406 p hpattern ((@Law4406.models_iff (Fin 8) (fam p)).mp hp)

/-- info: 'Equation4406_not_structuralFromFin_Equation4401_nonabelianDicyclic8A2B2Witness6387' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4406_not_structuralFromFin_Equation4401_nonabelianDicyclic8A2B2Witness6387._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target4406._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4406_not_structuralFromFin_Equation4401_nonabelianDicyclic8A2B2Witness6387

