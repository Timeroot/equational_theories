import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field13Index4Source17

def genData : Array (Array (Fin 13)) := #[#[0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0], #[0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4], #[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
def gen (i : Fin 4) (x : Fin 13) : Fin 13 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 13)) := #[#[0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4], #[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0]]
def genInv (i : Fin 4) (x : Fin 13) : Fin 13 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 13)) := #[#[0, 4, 8, 12, 3, 7, 11, 2, 6, 10, 1, 5, 9]]
def probe (i : Fin 1) (x : Fin 13) : Fin 13 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 13)) := #[#[0, 10, 7, 4, 1, 11, 8, 5, 2, 12, 9, 6, 3]]
def probeInv (i : Fin 1) (x : Fin 13) : Fin 13 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 13)) := #[#[0, 0, 0, 0, 0, 0, 0, 12, 10, 0, 0, 4, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 0, 11, 1, 1, 5], #[6, 2, 2, 2, 2, 2, 2, 2, 2, 1, 12, 2, 2], #[3, 7, 3, 3, 3, 3, 3, 3, 3, 3, 2, 0, 3], #[4, 4, 8, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1], #[2, 5, 5, 9, 5, 5, 5, 5, 5, 5, 5, 5, 4], #[5, 3, 6, 6, 10, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 6, 4, 7, 7, 11, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 7, 5, 8, 8, 12, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 8, 6, 9, 9, 0, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 9, 7, 10, 10, 1, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 10, 8, 11, 11, 2, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 11, 9, 12, 12, 3, 12, 12]]
def sourceRow (i : Fin 13) (x : Fin 13) : Fin 13 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 13) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 13) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [1], [3], [0, 1], [1, 1], [2, 1], [0, 3], [2, 3], [3, 3], [0, 1, 1], [2, 1, 1], [3, 2, 1], [0, 3, 3], [1, 1, 2, 3, 3, 2, 1], [2], [1, 0], [3, 0], [1, 2], [3, 2], [0, 1, 0], [1, 1, 0], [2, 1, 0], [0, 3, 0], [2, 3, 0], [3, 3, 0], [1, 0, 1], [1, 1, 1], [1, 1, 2], [2, 1, 2], [0, 3, 2], [3, 3, 2], [0, 1, 1, 0], [2, 1, 1, 0], [3, 2, 1, 0], [0, 3, 3, 0], [1, 1, 0, 1], [0, 1, 1, 2], [3, 2, 1, 2], [0, 3, 3, 2]]
def words (i : Fin 39) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 13 × Fin 13) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 7)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 39)) := #[#[(0, 0), (1, 0), (2, 0), (1, 13), (3, 0), (2, 14), (2, 13), (4, 0), (4, 13), (1, 14), (3, 14), (4, 14), (3, 13)], #[(3, 15), (0, 1), (1, 1), (2, 1), (1, 15), (3, 1), (2, 17), (2, 15), (4, 1), (4, 15), (1, 17), (3, 17), (4, 17)], #[(4, 27), (3, 20), (0, 4), (1, 4), (2, 4), (1, 20), (3, 4), (2, 27), (2, 20), (4, 4), (4, 20), (1, 27), (3, 27)], #[(3, 19), (4, 19), (3, 3), (0, 3), (1, 26), (2, 26), (1, 3), (3, 26), (2, 19), (2, 3), (4, 26), (4, 3), (1, 19)], #[(1, 7), (3, 7), (4, 7), (3, 25), (0, 7), (1, 23), (2, 23), (1, 25), (3, 23), (2, 7), (2, 25), (4, 23), (4, 25)], #[(4, 35), (1, 10), (3, 10), (4, 10), (3, 35), (0, 10), (1, 32), (2, 32), (1, 35), (3, 32), (2, 10), (2, 35), (4, 32)], #[(4, 36), (4, 9), (1, 31), (3, 31), (4, 31), (3, 9), (0, 9), (1, 36), (2, 36), (1, 9), (3, 36), (2, 31), (2, 9)], #[(2, 12), (4, 38), (4, 12), (1, 34), (3, 34), (4, 34), (3, 12), (0, 12), (1, 38), (2, 38), (1, 12), (3, 38), (2, 34)], #[(2, 11), (2, 37), (4, 33), (4, 37), (1, 11), (3, 11), (4, 11), (3, 37), (0, 11), (1, 33), (2, 33), (1, 37), (3, 33)], #[(3, 21), (2, 5), (2, 28), (4, 21), (4, 28), (1, 5), (3, 5), (4, 5), (3, 28), (0, 5), (1, 21), (2, 21), (1, 28)], #[(1, 6), (3, 29), (2, 22), (2, 6), (4, 29), (4, 6), (1, 22), (3, 22), (4, 22), (3, 6), (0, 6), (1, 29), (2, 29)], #[(2, 8), (1, 24), (3, 8), (2, 30), (2, 24), (4, 8), (4, 24), (1, 30), (3, 30), (4, 30), (3, 24), (0, 8), (1, 8)], #[(1, 2), (2, 2), (1, 16), (3, 2), (2, 18), (2, 16), (4, 2), (4, 16), (1, 18), (3, 18), (4, 18), (3, 16), (0, 2)]]
def tr (x y : Fin 13) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![1, 13, 13, 13, 13]
def valuesData : Array (Array (Fin 13)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 13 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 39)) := #[#[13], #[0], #[0], #[0], #[0]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 39 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 13) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 13) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 13)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target838 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation838 (Fin 13) (fam p) := by native_decide

theorem target3264 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3264 (Fin 13) (fam p) := by native_decide

end Magma.Field13Index4Source17

open Magma.Field13Index4Source17

theorem Equation838_not_structuralFromFin_Equation3317_field13Index4Source17 : ¬ Law838.StructuralFromFin Law3317 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3317.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target838 p hpattern ((@Law838.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation838_not_structuralFromFin_Equation3317_field13Index4Source17' depends on axioms: [propext, Classical.choice, Quot.sound, Equation838_not_structuralFromFin_Equation3317_field13Index4Source17._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target838._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation838_not_structuralFromFin_Equation3317_field13Index4Source17

theorem Equation3264_not_structuralFromFin_Equation3317_field13Index4Source17 : ¬ Law3264.StructuralFromFin Law3317 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3317.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3264 p hpattern ((@Law3264.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3264_not_structuralFromFin_Equation3317_field13Index4Source17' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3264_not_structuralFromFin_Equation3317_field13Index4Source17._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3264._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3264_not_structuralFromFin_Equation3317_field13Index4Source17

