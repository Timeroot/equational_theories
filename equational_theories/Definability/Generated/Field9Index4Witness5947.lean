import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field9Index4Witness5947

def genData : Array (Array (Fin 9)) := #[#[1, 2, 0, 4, 5, 3, 7, 8, 6], #[3, 4, 5, 6, 7, 8, 0, 1, 2], #[0, 2, 1, 6, 8, 7, 3, 5, 4], #[2, 0, 1, 5, 3, 4, 8, 6, 7], #[6, 7, 8, 0, 1, 2, 3, 4, 5]]
def gen (i : Fin 5) (x : Fin 9) : Fin 9 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 9)) := #[#[2, 0, 1, 5, 3, 4, 8, 6, 7], #[6, 7, 8, 0, 1, 2, 3, 4, 5], #[0, 2, 1, 6, 8, 7, 3, 5, 4], #[1, 2, 0, 4, 5, 3, 7, 8, 6], #[3, 4, 5, 6, 7, 8, 0, 1, 2]]
def genInv (i : Fin 5) (x : Fin 9) : Fin 9 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 9)) := #[#[0, 3, 6, 2, 5, 8, 1, 4, 7]]
def probe (i : Fin 1) (x : Fin 9) : Fin 9 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 9)) := #[#[0, 6, 3, 1, 7, 4, 2, 8, 5]]
def probeInv (i : Fin 1) (x : Fin 9) : Fin 9 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 9)) := #[#[0, 7, 5, 3, 1, 8, 6, 4, 2], #[3, 1, 8, 6, 4, 2, 0, 7, 5], #[6, 4, 2, 0, 7, 5, 3, 1, 8], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[3, 1, 8, 6, 4, 2, 0, 7, 5], #[6, 4, 2, 0, 7, 5, 3, 1, 8], #[0, 7, 5, 3, 1, 8, 6, 4, 2], #[3, 1, 8, 6, 4, 2, 0, 7, 5], #[6, 4, 2, 0, 7, 5, 3, 1, 8]]
def sourceRow (i : Fin 9) (x : Fin 9) : Fin 9 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 9) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 9) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [0], [1], [3], [4], [1, 0], [4, 0], [3, 1], [4, 3], [3, 4, 2, 4, 3], [2, 0], [2, 1], [0, 2], [1, 2], [2, 1, 0], [1, 2, 0], [0, 2, 1], [1, 0, 2]]
def words (i : Fin 18) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 9 × Fin 9) := #[(0, 0), (0, 1), (0, 3), (0, 4), (0, 5)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 18)) := #[#[(0, 0), (1, 0), (1, 9), (2, 0), (3, 0), (4, 0), (2, 9), (4, 9), (3, 9)], #[(1, 12), (0, 1), (1, 1), (4, 1), (2, 1), (3, 1), (3, 12), (2, 12), (4, 12)], #[(1, 3), (1, 10), (0, 3), (3, 3), (4, 3), (2, 3), (4, 10), (3, 10), (2, 10)], #[(2, 13), (4, 13), (3, 13), (0, 2), (1, 2), (1, 13), (2, 2), (3, 2), (4, 2)], #[(3, 17), (2, 17), (4, 17), (1, 17), (0, 5), (1, 5), (4, 5), (2, 5), (3, 5)], #[(4, 15), (3, 15), (2, 15), (1, 7), (1, 15), (0, 7), (3, 7), (4, 7), (2, 7)], #[(2, 4), (3, 4), (4, 4), (2, 11), (4, 11), (3, 11), (0, 4), (1, 4), (1, 11)], #[(4, 6), (2, 6), (3, 6), (3, 16), (2, 16), (4, 16), (1, 16), (0, 6), (1, 6)], #[(3, 8), (4, 8), (2, 8), (4, 14), (3, 14), (2, 14), (1, 8), (1, 14), (0, 8)]]
def tr (x y : Fin 9) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![1, 9, 9, 9, 9]
def valuesData : Array (Array (Fin 9)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 9 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 18)) := #[#[9], #[0], #[0], #[0], #[0]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 18 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 9) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 9) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 9)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target4406 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation4406 (Fin 9) (fam p) := by native_decide

end Magma.Field9Index4Witness5947

open Magma.Field9Index4Witness5947

theorem Equation4406_not_structuralFromFin_Equation727_field9Index4Witness5947 : ¬ Law4406.StructuralFromFin Law727 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law727.models_iff (Fin 9) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target4406 p hpattern ((@Law4406.models_iff (Fin 9) (fam p)).mp hp)

/-- info: 'Equation4406_not_structuralFromFin_Equation727_field9Index4Witness5947' depends on axioms: [propext, Classical.choice, Quot.sound, Equation4406_not_structuralFromFin_Equation727_field9Index4Witness5947._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target4406._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4406_not_structuralFromFin_Equation727_field9Index4Witness5947

