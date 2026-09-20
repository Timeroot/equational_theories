import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Affine13Index3

def genData : Array (Array (Fin 13)) := #[#[0, 8, 3, 11, 6, 1, 9, 4, 12, 7, 2, 10, 5], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0], #[0, 5, 10, 2, 7, 12, 4, 9, 1, 6, 11, 3, 8], #[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
def gen (i : Fin 4) (x : Fin 13) : Fin 13 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 13)) := #[#[0, 5, 10, 2, 7, 12, 4, 9, 1, 6, 11, 3, 8], #[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 8, 3, 11, 6, 1, 9, 4, 12, 7, 2, 10, 5], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0]]
def genInv (i : Fin 4) (x : Fin 13) : Fin 13 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 13)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 11]]
def probe (i : Fin 1) (x : Fin 13) : Fin 13 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 13)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 11]]
def probeInv (i : Fin 1) (x : Fin 13) : Fin 13 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 13)) := #[#[0, 10, 0, 0, 0, 11, 0, 0, 2, 0, 0, 0, 3], #[4, 1, 11, 1, 1, 1, 12, 1, 1, 3, 1, 1, 1], #[2, 5, 2, 12, 2, 2, 2, 0, 2, 2, 4, 2, 2], #[3, 3, 6, 3, 0, 3, 3, 3, 1, 3, 3, 5, 3], #[4, 4, 4, 7, 4, 1, 4, 4, 4, 2, 4, 4, 6], #[7, 5, 5, 5, 8, 5, 2, 5, 5, 5, 3, 5, 5], #[6, 8, 6, 6, 6, 9, 6, 3, 6, 6, 6, 4, 6], #[7, 7, 9, 7, 7, 7, 10, 7, 4, 7, 7, 7, 5], #[6, 8, 8, 10, 8, 8, 8, 11, 8, 5, 8, 8, 8], #[9, 7, 9, 9, 11, 9, 9, 9, 12, 9, 6, 9, 9], #[10, 10, 8, 10, 10, 12, 10, 10, 10, 0, 10, 7, 10], #[11, 11, 11, 9, 11, 11, 0, 11, 11, 11, 1, 11, 8], #[9, 12, 12, 12, 10, 12, 12, 1, 12, 12, 12, 2, 12]]
def sourceRow (i : Fin 13) (x : Fin 13) : Fin 13 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 13) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 13) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [1], [3], [0, 1], [1, 1], [2, 1], [3, 3], [1, 0, 1], [3, 0, 1], [0, 1, 1], [2, 1, 1], [1, 2, 1], [3, 2, 1], [3, 2, 1, 2, 3, 2, 1], [2], [0, 0], [1, 0], [3, 0], [1, 2], [3, 2], [0, 3], [2, 3], [1, 0, 0], [3, 0, 0], [0, 1, 0], [1, 1, 0], [2, 1, 0], [0, 3, 0], [2, 3, 0], [3, 3, 0], [1, 1, 1], [1, 1, 2], [3, 3, 2], [1, 0, 3], [3, 0, 3], [1, 2, 3], [3, 2, 3], [0, 3, 3], [2, 3, 3], [3, 3, 3], [1, 1, 0, 0], [3, 3, 0, 0], [1, 0, 1, 0], [3, 0, 1, 0], [0, 1, 1, 0], [1, 2, 1, 0], [3, 2, 1, 0], [1, 0, 3, 0], [3, 0, 3, 0], [1, 2, 3, 0], [3, 2, 3, 0], [0, 3, 3, 0]]
def words (i : Fin 52) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 13 × Fin 13) := #[(0, 0), (0, 1), (0, 2), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 52)) := #[#[(0, 0), (1, 0), (2, 0), (2, 13), (3, 0), (1, 14), (3, 13), (3, 14), (1, 13), (3, 15), (2, 14), (2, 15), (1, 15)], #[(1, 22), (0, 1), (1, 1), (2, 1), (2, 16), (3, 1), (1, 18), (3, 16), (3, 18), (1, 16), (3, 22), (2, 18), (2, 22)], #[(2, 40), (1, 40), (0, 4), (1, 4), (2, 4), (2, 25), (3, 4), (1, 31), (3, 25), (3, 31), (1, 25), (3, 40), (2, 31)], #[(2, 38), (2, 44), (1, 44), (0, 9), (1, 30), (2, 30), (2, 9), (3, 30), (1, 38), (3, 9), (3, 38), (1, 9), (3, 44)], #[(3, 48), (2, 12), (2, 48), (1, 48), (0, 12), (1, 46), (2, 46), (2, 34), (3, 46), (1, 12), (3, 34), (3, 12), (1, 34)], #[(1, 20), (3, 27), (2, 5), (2, 27), (1, 27), (0, 5), (1, 26), (2, 26), (2, 20), (3, 26), (1, 5), (3, 20), (3, 5)], #[(3, 11), (1, 33), (3, 47), (2, 11), (2, 47), (1, 47), (0, 11), (1, 45), (2, 45), (2, 33), (3, 45), (1, 11), (3, 33)], #[(3, 8), (3, 36), (1, 8), (3, 43), (2, 36), (2, 43), (1, 43), (0, 8), (1, 50), (2, 50), (2, 8), (3, 50), (1, 36)], #[(1, 21), (3, 3), (3, 21), (1, 3), (3, 24), (2, 21), (2, 24), (1, 24), (0, 3), (1, 28), (2, 28), (2, 3), (3, 28)], #[(3, 49), (1, 35), (3, 7), (3, 35), (1, 7), (3, 42), (2, 35), (2, 42), (1, 42), (0, 7), (1, 49), (2, 49), (2, 7)], #[(2, 37), (3, 39), (1, 10), (3, 37), (3, 10), (1, 37), (3, 51), (2, 10), (2, 51), (1, 51), (0, 10), (1, 39), (2, 39)], #[(2, 6), (2, 29), (3, 6), (1, 32), (3, 29), (3, 32), (1, 29), (3, 41), (2, 32), (2, 41), (1, 41), (0, 6), (1, 6)], #[(1, 2), (2, 2), (2, 17), (3, 2), (1, 19), (3, 17), (3, 19), (1, 17), (3, 23), (2, 19), (2, 23), (1, 23), (0, 2)]]
def tr (x y : Fin 13) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![1, 13, 13, 13]
def valuesData : Array (Array (Fin 13)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 13 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 52)) := #[#[13], #[0], #[0], #[0]]
def stabilizers (i : Fin 4) (j : Fin 1) : Fin 52 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 13) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 13) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 13)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target1227 : ∀ p : Params, @Equation1227 (Fin 13) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1230 : ∀ p : Params, @Equation1230 (Fin 13) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target1633 : ∀ p : Params, @Equation1633 (Fin 13) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target3460 : ∀ p : Params, @Equation3460 (Fin 13) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

theorem target3723 : ∀ p : Params, @Equation3723 (Fin 13) (fam p) → ¬ Pattern (fam p) probePerm pattern := by native_decide

end Magma.Affine13Index3

open Magma.Affine13Index3

theorem Equation1633_not_structuralFromFin_Equation827_affine13Index3 : ¬ Law1633.StructuralFromFin Law827 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law827.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1633 p ((@Law1633.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation1633_not_structuralFromFin_Equation827_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1633_not_structuralFromFin_Equation827_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1633._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1633_not_structuralFromFin_Equation827_affine13Index3

theorem Equation3460_not_structuralFromFin_Equation827_affine13Index3 : ¬ Law3460.StructuralFromFin Law827 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law827.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3460 p ((@Law3460.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3460_not_structuralFromFin_Equation827_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3460_not_structuralFromFin_Equation827_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3460._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3460_not_structuralFromFin_Equation827_affine13Index3

theorem Equation1227_not_structuralFromFin_Equation837_affine13Index3 : ¬ Law1227.StructuralFromFin Law837 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law837.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1227 p ((@Law1227.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation1227_not_structuralFromFin_Equation837_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1227_not_structuralFromFin_Equation837_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1227._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1227_not_structuralFromFin_Equation837_affine13Index3

theorem Equation1230_not_structuralFromFin_Equation837_affine13Index3 : ¬ Law1230.StructuralFromFin Law837 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law837.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1230 p ((@Law1230.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation1230_not_structuralFromFin_Equation837_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1230_not_structuralFromFin_Equation837_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1230._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1230_not_structuralFromFin_Equation837_affine13Index3

theorem Equation3460_not_structuralFromFin_Equation837_affine13Index3 : ¬ Law3460.StructuralFromFin Law837 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law837.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3460 p ((@Law3460.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3460_not_structuralFromFin_Equation837_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3460_not_structuralFromFin_Equation837_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3460._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3460_not_structuralFromFin_Equation837_affine13Index3

theorem Equation3723_not_structuralFromFin_Equation837_affine13Index3 : ¬ Law3723.StructuralFromFin Law837 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law837.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3723 p ((@Law3723.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3723_not_structuralFromFin_Equation837_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3723_not_structuralFromFin_Equation837_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3723._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3723_not_structuralFromFin_Equation837_affine13Index3

theorem Equation1227_not_structuralFromFin_Equation1259_affine13Index3 : ¬ Law1227.StructuralFromFin Law1259 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1259.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1227 p ((@Law1227.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation1227_not_structuralFromFin_Equation1259_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1227_not_structuralFromFin_Equation1259_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1227._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1227_not_structuralFromFin_Equation1259_affine13Index3

theorem Equation1230_not_structuralFromFin_Equation1259_affine13Index3 : ¬ Law1230.StructuralFromFin Law1259 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1259.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1230 p ((@Law1230.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation1230_not_structuralFromFin_Equation1259_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1230_not_structuralFromFin_Equation1259_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1230._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1230_not_structuralFromFin_Equation1259_affine13Index3

theorem Equation3460_not_structuralFromFin_Equation1259_affine13Index3 : ¬ Law3460.StructuralFromFin Law1259 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1259.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3460 p ((@Law3460.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3460_not_structuralFromFin_Equation1259_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3460_not_structuralFromFin_Equation1259_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3460._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3460_not_structuralFromFin_Equation1259_affine13Index3

theorem Equation3723_not_structuralFromFin_Equation1259_affine13Index3 : ¬ Law3723.StructuralFromFin Law1259 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1259.models_iff (Fin 13) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3723 p ((@Law3723.models_iff (Fin 13) (fam p)).mp hp)

/-- info: 'Equation3723_not_structuralFromFin_Equation1259_affine13Index3' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3723_not_structuralFromFin_Equation1259_affine13Index3._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3723._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3723_not_structuralFromFin_Equation1259_affine13Index3

