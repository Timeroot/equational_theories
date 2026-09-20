import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field13Index4Source1

def genData : Array (Array (Fin 13)) := #[#[0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4], #[1, 4, 7, 10, 0, 3, 6, 9, 12, 2, 5, 8, 11], #[0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10], #[4, 0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8]]
def gen (i : Fin 4) (x : Fin 13) : Fin 13 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 13)) := #[#[0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10], #[4, 0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8], #[0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4], #[1, 4, 7, 10, 0, 3, 6, 9, 12, 2, 5, 8, 11]]
def genInv (i : Fin 4) (x : Fin 13) : Fin 13 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 13)) := #[#[0, 4, 8, 12, 3, 7, 11, 2, 6, 10, 1, 5, 9]]
def probe (i : Fin 1) (x : Fin 13) : Fin 13 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 13)) := #[#[0, 10, 7, 4, 1, 11, 8, 5, 2, 12, 9, 6, 3]]
def probeInv (i : Fin 1) (x : Fin 13) : Fin 13 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 13)) := #[#[0, 0, 0, 0, 0, 0, 0, 9, 1, 0, 0, 3, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 1, 4], #[5, 2, 2, 2, 2, 2, 2, 2, 2, 11, 3, 2, 2], #[3, 6, 3, 3, 3, 3, 3, 3, 3, 3, 12, 4, 3], #[4, 4, 7, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5], #[6, 5, 5, 8, 5, 5, 5, 5, 5, 5, 5, 5, 1], #[2, 7, 6, 6, 9, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 3, 8, 7, 7, 10, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 4, 9, 8, 8, 11, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 5, 10, 9, 9, 12, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 6, 11, 10, 10, 0, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 7, 12, 11, 11, 1, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 8, 0, 12, 12, 2, 12, 12]]
def sourceRow (i : Fin 13) (x : Fin 13) : Fin 13 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 13) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 13) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [1], [3], [0, 1], [2, 1], [0, 3], [2, 3], [1, 0, 1], [3, 0, 1], [3, 2, 1], [1, 2, 3], [3, 2, 3], [2, 1, 0, 1], [3, 2, 3, 0, 3, 2, 1, 0, 1], [2], [1, 0], [3, 0], [1, 2], [3, 2], [0, 1, 0], [2, 1, 0], [0, 3, 0], [2, 3, 0], [0, 1, 2], [2, 1, 2], [0, 3, 2], [2, 3, 2], [1, 0, 3], [1, 0, 1, 0], [3, 0, 1, 0], [3, 2, 1, 0], [1, 2, 3, 0], [3, 2, 3, 0], [2, 3, 0, 1], [0, 3, 2, 1], [2, 3, 2, 1], [3, 0, 1, 2], [1, 2, 3, 2], [0, 1, 0, 3]]
def words (i : Fin 39) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 13 × Fin 13) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 7)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 39)) := #[#[(0, 0), (1, 0), (2, 0), (1, 14), (3, 0), (2, 13), (2, 14), (4, 0), (4, 14), (1, 13), (3, 13), (4, 13), (3, 14)], #[(3, 1), (0, 1), (1, 15), (2, 15), (1, 1), (3, 15), (2, 17), (2, 1), (4, 15), (4, 1), (1, 17), (3, 17), (4, 17)], #[(4, 35), (3, 7), (0, 7), (1, 28), (2, 28), (1, 7), (3, 28), (2, 35), (2, 7), (4, 28), (4, 7), (1, 35), (3, 35)], #[(3, 4), (4, 4), (3, 20), (0, 4), (1, 24), (2, 24), (1, 20), (3, 24), (2, 4), (2, 20), (4, 24), (4, 20), (1, 4)], #[(1, 2), (3, 2), (4, 2), (3, 16), (0, 2), (1, 18), (2, 18), (1, 16), (3, 18), (2, 2), (2, 16), (4, 18), (4, 16)], #[(4, 9), (1, 27), (3, 27), (4, 27), (3, 9), (0, 9), (1, 30), (2, 30), (1, 9), (3, 30), (2, 27), (2, 9), (4, 30)], #[(4, 34), (4, 38), (1, 12), (3, 12), (4, 12), (3, 38), (0, 12), (1, 34), (2, 34), (1, 38), (3, 34), (2, 12), (2, 38)], #[(2, 29), (4, 36), (4, 29), (1, 8), (3, 8), (4, 8), (3, 29), (0, 8), (1, 36), (2, 36), (1, 29), (3, 36), (2, 8)], #[(2, 11), (2, 32), (4, 33), (4, 32), (1, 11), (3, 11), (4, 11), (3, 32), (0, 11), (1, 33), (2, 33), (1, 32), (3, 33)], #[(3, 3), (2, 19), (2, 23), (4, 3), (4, 23), (1, 19), (3, 19), (4, 19), (3, 23), (0, 3), (1, 3), (2, 3), (1, 23)], #[(1, 5), (3, 21), (2, 25), (2, 5), (4, 21), (4, 5), (1, 25), (3, 25), (4, 25), (3, 5), (0, 5), (1, 21), (2, 21)], #[(2, 31), (1, 10), (3, 31), (2, 37), (2, 10), (4, 31), (4, 10), (1, 37), (3, 37), (4, 37), (3, 10), (0, 10), (1, 31)], #[(1, 6), (2, 6), (1, 26), (3, 6), (2, 22), (2, 26), (4, 6), (4, 26), (1, 22), (3, 22), (4, 22), (3, 26), (0, 6)]]
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

theorem target3723 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3723 (Fin 13) (fam p) := by native_decide

end Magma.Field13Index4Source1

open Magma.Field13Index4Source1

theorem Equation838_not_structuralFromFin_Equation103_field13Index4Source1 : ¬ Law838.StructuralFromFin Law103 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law103.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target838 p hpattern ((@Law838.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation838_not_structuralFromFin_Equation103_field13Index4Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation838_not_structuralFromFin_Equation103_field13Index4Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target838._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation838_not_structuralFromFin_Equation103_field13Index4Source1

theorem Equation3723_not_structuralFromFin_Equation103_field13Index4Source1 : ¬ Law3723.StructuralFromFin Law103 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law103.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3723 p hpattern ((@Law3723.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3723_not_structuralFromFin_Equation103_field13Index4Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3723_not_structuralFromFin_Equation103_field13Index4Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3723._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3723_not_structuralFromFin_Equation103_field13Index4Source1

theorem Equation838_not_structuralFromFin_Equation1230_field13Index4Source1 : ¬ Law838.StructuralFromFin Law1230 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1230.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target838 p hpattern ((@Law838.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation838_not_structuralFromFin_Equation1230_field13Index4Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation838_not_structuralFromFin_Equation1230_field13Index4Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target838._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation838_not_structuralFromFin_Equation1230_field13Index4Source1

theorem Equation838_not_structuralFromFin_Equation1235_field13Index4Source1 : ¬ Law838.StructuralFromFin Law1235 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1235.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target838 p hpattern ((@Law838.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation838_not_structuralFromFin_Equation1235_field13Index4Source1' depends on axioms: [propext, Classical.choice, Quot.sound, Equation838_not_structuralFromFin_Equation1235_field13Index4Source1._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target838._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation838_not_structuralFromFin_Equation1235_field13Index4Source1

