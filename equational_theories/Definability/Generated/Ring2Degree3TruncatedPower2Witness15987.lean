import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Ring2Degree3TruncatedPower2Witness15987

def genData : Array (Array (Fin 8)) := #[#[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[4, 5, 6, 7, 0, 1, 2, 3], #[0, 5, 2, 7, 4, 1, 6, 3], #[0, 3, 2, 1, 4, 7, 6, 5]]
def gen (i : Fin 5) (x : Fin 8) : Fin 8 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 8)) := #[#[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[4, 5, 6, 7, 0, 1, 2, 3], #[0, 5, 2, 7, 4, 1, 6, 3], #[0, 3, 2, 1, 4, 7, 6, 5]]
def genInv (i : Fin 5) (x : Fin 8) : Fin 8 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 8)) := #[#[0, 3, 6, 5, 4, 7, 2, 1], #[0, 1, 4, 5, 2, 3, 6, 7], #[0, 1, 2, 3, 6, 7, 4, 5]]
def probe (i : Fin 3) (x : Fin 8) : Fin 8 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 8)) := #[#[0, 7, 6, 1, 4, 3, 2, 5], #[0, 1, 4, 5, 2, 3, 6, 7], #[0, 1, 2, 3, 6, 7, 4, 5]]
def probeInv (i : Fin 3) (x : Fin 8) : Fin 8 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 8)) := #[#[6, 4, 6, 4, 6, 4, 6, 4], #[5, 7, 5, 7, 5, 7, 5, 7], #[4, 6, 4, 6, 4, 6, 4, 6], #[7, 5, 7, 5, 7, 5, 7, 5], #[2, 0, 2, 0, 2, 0, 2, 0], #[1, 3, 1, 3, 1, 3, 1, 3], #[0, 2, 0, 2, 0, 2, 0, 2], #[3, 1, 3, 1, 3, 1, 3, 1]]
def sourceRow (i : Fin 8) (x : Fin 8) : Fin 8 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 8) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 3) : Equiv.Perm (Fin 8) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [0], [1], [2], [1, 0], [2, 0], [2, 1], [2, 1, 0], [0, 1, 3, 2, 1, 0], [4], [3, 0], [4, 0], [3, 1], [4, 1], [3, 2], [4, 2], [0, 3], [4, 3], [0, 4], [3, 1, 0], [4, 2, 0], [4, 3, 0], [3, 2, 1], [4, 2, 1], [0, 3, 1], [4, 3, 1], [4, 3, 2], [0, 4, 2], [4, 0, 3], [0, 4, 3], [3, 0, 4], [0, 4, 3, 0]]
def words (i : Fin 32) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 8 × Fin 8) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 6)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 32)) := #[#[(0, 0), (1, 0), (2, 0), (1, 9), (3, 0), (1, 8), (4, 0), (1, 17)], #[(1, 1), (0, 1), (1, 18), (2, 1), (1, 16), (3, 1), (1, 29), (4, 1)], #[(2, 2), (1, 13), (0, 2), (1, 2), (4, 2), (1, 25), (3, 2), (1, 12)], #[(1, 11), (2, 4), (1, 4), (0, 4), (1, 28), (4, 4), (1, 24), (3, 4)], #[(3, 3), (1, 14), (4, 3), (1, 26), (0, 3), (1, 3), (2, 3), (1, 15)], #[(1, 10), (3, 5), (1, 30), (4, 5), (1, 5), (0, 5), (1, 27), (2, 5)], #[(4, 6), (1, 31), (3, 6), (1, 22), (2, 6), (1, 23), (0, 6), (1, 6)], #[(1, 21), (4, 7), (1, 19), (3, 7), (1, 20), (2, 7), (1, 7), (0, 7)]]
def tr (x y : Fin 8) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![4, 8, 4, 4, 4]
def valuesData : Array (Array (Fin 8)) := #[#[0, 2, 4, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 4, 6], #[0, 2, 4, 6], #[0, 2, 4, 6]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 8 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 32)) := #[#[8], #[0], #[8], #[8], #[8]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 32 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def pattern : Fin 3 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 8)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target3556 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3556 (Fin 8) (fam p) := by native_decide

end Magma.Ring2Degree3TruncatedPower2Witness15987

open Magma.Ring2Degree3TruncatedPower2Witness15987

theorem Equation3556_not_structuralFromFin_Equation327_ring2Degree3TruncatedPower2Witness15987 : ¬ Law3556.StructuralFromFin Law327 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law327.models_iff (Fin 8) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3556 p hpattern ((@Law3556.models_iff (Fin 8) (fam p)).mp hp)

/-- info: 'Equation3556_not_structuralFromFin_Equation327_ring2Degree3TruncatedPower2Witness15987' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3556_not_structuralFromFin_Equation327_ring2Degree3TruncatedPower2Witness15987._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 target3556._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3556_not_structuralFromFin_Equation327_ring2Degree3TruncatedPower2Witness15987

