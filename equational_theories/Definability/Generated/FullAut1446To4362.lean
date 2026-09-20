import DefOrbit.Generated.NativeFullAut1446To4362
import equational_theories.Definability.NativeOrbit

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.FullAut1446To4362

def genData : Array (Array (Fin 12)) := #[#[0, 1, 2, 9, 10, 11, 6, 7, 8, 3, 4, 5], #[1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9], #[3, 4, 5, 0, 1, 2, 9, 10, 11, 6, 7, 8], #[2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10]]
def gen (i : Fin 4) (x : Fin 12) : Fin 12 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 12)) := #[#[0, 1, 2, 9, 10, 11, 6, 7, 8, 3, 4, 5], #[2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10], #[3, 4, 5, 0, 1, 2, 9, 10, 11, 6, 7, 8], #[1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9]]
def genInv (i : Fin 4) (x : Fin 12) : Fin 12 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 12)) := #[#[0, 1, 2, 4, 5, 3, 6, 7, 8, 10, 11, 9], #[0, 1, 8, 3, 4, 5, 6, 7, 2, 9, 10, 11]]
def probe (i : Fin 2) (x : Fin 12) : Fin 12 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 12)) := #[#[0, 1, 2, 5, 3, 4, 6, 7, 8, 11, 9, 10], #[0, 1, 8, 3, 4, 5, 6, 7, 2, 9, 10, 11]]
def probeInv (i : Fin 2) (x : Fin 12) : Fin 12 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 12)) := #[#[7, 8, 7, 7, 8, 8, 8, 8, 8, 7, 8, 8], #[8, 8, 6, 6, 8, 6, 6, 6, 6, 6, 8, 6], #[7, 6, 6, 7, 7, 6, 7, 7, 7, 7, 7, 6], #[10, 11, 11, 10, 11, 10, 10, 11, 11, 11, 11, 11], #[9, 11, 9, 11, 11, 9, 9, 11, 9, 9, 9, 9], #[10, 10, 9, 10, 9, 9, 10, 10, 9, 10, 10, 10], #[2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2], #[0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0], #[1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0], #[4, 5, 5, 5, 5, 5, 4, 5, 5, 4, 5, 4], #[3, 5, 3, 3, 3, 3, 3, 5, 3, 5, 5, 3], #[4, 4, 3, 4, 4, 4, 4, 4, 3, 4, 3, 3]]
def sourceRow (i : Fin 12) (x : Fin 12) : Fin 12 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 12) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 2) : Equiv.Perm (Fin 12) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [1], [2], [3], [2, 1], [0, 2], [3, 2], [0, 2, 1], [2, 0, 2], [3, 0, 2], [2, 0, 2, 1], [3, 2, 0, 2], [2, 0, 2, 1, 0, 3, 2, 0, 2], [1, 0], [2, 0], [3, 0], [2, 1, 0], [0, 2, 0], [3, 2, 0], [0, 2, 1, 0], [2, 0, 2, 0], [3, 0, 2, 0], [2, 0, 2, 1, 0], [3, 2, 0, 2, 0]]
def words (i : Fin 24) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 12 × Fin 12) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)]
def rep (i : Fin 9) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 9 × Fin 24)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (3, 12), (4, 12), (5, 12)], #[(2, 1), (0, 1), (1, 1), (5, 1), (3, 1), (4, 1), (8, 1), (6, 1), (7, 1), (5, 13), (3, 13), (4, 13)], #[(1, 3), (2, 3), (0, 3), (4, 3), (5, 3), (3, 3), (7, 3), (8, 3), (6, 3), (4, 15), (5, 15), (3, 15)], #[(3, 2), (4, 2), (5, 2), (0, 2), (1, 2), (2, 2), (3, 14), (4, 14), (5, 14), (6, 2), (7, 2), (8, 2)], #[(5, 4), (3, 4), (4, 4), (2, 4), (0, 4), (1, 4), (5, 16), (3, 16), (4, 16), (8, 4), (6, 4), (7, 4)], #[(4, 6), (5, 6), (3, 6), (1, 6), (2, 6), (0, 6), (4, 18), (5, 18), (3, 18), (7, 6), (8, 6), (6, 6)], #[(6, 8), (7, 8), (8, 8), (3, 8), (4, 8), (5, 8), (0, 8), (1, 8), (2, 8), (3, 20), (4, 20), (5, 20)], #[(8, 10), (6, 10), (7, 10), (5, 10), (3, 10), (4, 10), (2, 10), (0, 10), (1, 10), (5, 22), (3, 22), (4, 22)], #[(7, 11), (8, 11), (6, 11), (4, 11), (5, 11), (3, 11), (1, 11), (2, 11), (0, 11), (4, 23), (5, 23), (3, 23)], #[(3, 5), (4, 5), (5, 5), (6, 5), (7, 5), (8, 5), (3, 17), (4, 17), (5, 17), (0, 5), (1, 5), (2, 5)], #[(5, 7), (3, 7), (4, 7), (8, 7), (6, 7), (7, 7), (5, 19), (3, 19), (4, 19), (2, 7), (0, 7), (1, 7)], #[(4, 9), (5, 9), (3, 9), (7, 9), (8, 9), (6, 9), (4, 21), (5, 21), (3, 21), (1, 9), (2, 9), (0, 9)]]
def tr (x y : Fin 12) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 9 → ℕ := ![6, 6, 6, 12, 12, 12, 6, 6, 6]
def valuesData : Array (Array (Fin 12)) := #[#[0, 1, 2, 6, 7, 8], #[0, 1, 2, 6, 7, 8], #[0, 1, 2, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 6, 7, 8], #[0, 1, 2, 6, 7, 8], #[0, 1, 2, 6, 7, 8]]
def values (i : Fin 9) (j : Fin (sizes i)) : Fin 12 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 24)) := #[#[12], #[12], #[12], #[0], #[0], #[0], #[12], #[12], #[12]]
def stabilizers (i : Fin 9) (j : Fin 1) : Fin 24 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 9) → Fin (sizes i)
def paramEquiv : Params ≃ (Fin 8748 × Fin 9216) :=
  finPiFinEquiv.trans ((finCongr (by decide)).trans (finProdFinEquiv (m := 8748) (n := 9216)).symm)
def imageData : Array (Array (Fin 12)) :=
  wordImageData genPerm words
def image (i : Fin 24) (x : Fin 12) : Fin 12 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 24) (x : Fin 12) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 12) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 12) := ⟨sourceRow⟩
def pattern : Fin 2 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 12)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

def places : Fin 9 → ℕ := ![1, 6, 36, 216, 2592, 31104, 373248, 2239488, 13436928]
private theorem sizes_pos : ∀ j, 0 < sizes j := by native_decide
private theorem places_correct : ∀ j : Fin 9,
    places j = ∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k) := by native_decide
def decodeNative (i : Fin 8748 × Fin 9216) : Params := fun j =>
  ⟨((i.2.val + 9216 * i.1.val) / places j) % sizes j, Nat.mod_lt _ (sizes_pos j)⟩
private theorem decodeNative_eq (i : Fin 8748 × Fin 9216) : decodeNative i = paramEquiv.symm i := by
  funext j
  apply Fin.ext
  change ((i.2.val + 9216 * i.1.val) / places j) % sizes j =
    ((i.2.val + 9216 * i.1.val) / (∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k))) % sizes j
  rw [places_correct]
private theorem native_orbit_correct : ∀ x y : Fin 12,
    DefOrbit.NativeFullAut1446To4362.orbitData.getD (x.val * 12 + y.val) 0 = (tr x y).1.val := by native_decide
private theorem native_places_correct : ∀ j : Fin 9,
    DefOrbit.NativeFullAut1446To4362.placesData.getD j.val 0 = places j := by native_decide
private theorem native_sizes_correct : ∀ j : Fin 9,
    DefOrbit.NativeFullAut1446To4362.sizesData.getD j.val 0 = sizes j := by native_decide
private theorem native_cell_correct : ∀ (x y : Fin 12) (v : Fin (sizes (tr x y).1)),
    (DefOrbit.NativeFullAut1446To4362.cellData.getD (x.val * 12 + y.val) #[]).getD v.val 0 =
      image (tr x y).2 (values (tr x y).1 v) := by native_decide
private theorem native_op_correct (i : Fin 8748 × Fin 9216) (x y : Fin 12) :
    DefOrbit.NativeFullAut1446To4362.op (i.2.val + 9216 * i.1.val) x y = (fam (paramEquiv.symm i)).op x y := by
  rw [← decodeNative_eq]
  unfold DefOrbit.NativeFullAut1446To4362.op
  dsimp only
  rw [native_orbit_correct, native_places_correct, native_sizes_correct]
  exact native_cell_correct x y (decodeNative i (tr x y).1)
private theorem native_probe_correct : ∀ i : Fin 2, ∀ x : Fin 12,
    DefOrbit.NativeFullAut1446To4362.probe i x = probePerm i x := by native_decide
private theorem native_pattern_correct (i : Fin 8748 × Fin 9216) :
    DefOrbit.NativeFullAut1446To4362.pattern (i.2.val + 9216 * i.1.val) ↔ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by
  unfold DefOrbit.NativeFullAut1446To4362.pattern Pattern pattern
  simp only [native_op_correct, native_probe_correct, Magma.IsEndo]
  simp

private abbrev test4362 (p : Params) : Prop := ∀ y z : Fin 12, ((fam p).op 0 ((fam p).op y z)) = ((fam p).op y ((fam p).op 0 z))
private theorem native_test4362_correct (i : Fin 8748 × Fin 9216) :
    DefOrbit.NativeFullAut1446To4362.test4362 (i.2.val + 9216 * i.1.val) ↔ test4362 (paramEquiv.symm i) := by
  unfold DefOrbit.NativeFullAut1446To4362.test4362 test4362
  simp only [native_op_correct]
private theorem native_checked4362 : DefOrbit.allBelow DefOrbit.NativeFullAut1446To4362.check4362 80621568 = true := by
  native_decide
private theorem restricted4362 : ∀ p : Params, test4362 p → ¬ Pattern (fam p) probePerm pattern := by
  have h : ∀ i : Fin 8748 × Fin 9216, test4362 (paramEquiv.symm i) →
      ¬ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by
    intro i
    have hi : i.2.val + 9216 * i.1.val < 80621568 := by omega
    have hc := (DefOrbit.allBelow_spec _ _).mp native_checked4362 _ hi
    have ht := of_decide_eq_true hc
    change DefOrbit.NativeFullAut1446To4362.test4362 (i.2.val + 9216 * i.1.val) → ¬ DefOrbit.NativeFullAut1446To4362.pattern (i.2.val + 9216 * i.1.val) at ht
    simpa only [native_test4362_correct, native_pattern_correct] using ht
  intro p
  simpa only [Equiv.symm_apply_apply] using h (paramEquiv p)
theorem target4362 : ∀ p : Params, @Equation4362 (Fin 12) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted4362 p (ht 0)

end Magma.FullAut1446To4362

open Magma.FullAut1446To4362

theorem Equation4362_not_structuralFromFin_Equation1446_fullAut1446To4362 : ¬ Law4362.StructuralFromFin Law1446 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1446.models_iff (Fin 12) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target4362 p ((@Law4362.models_iff (Fin 12) (fam p)).mp hp)

/-- info: 'Equation4362_not_structuralFromFin_Equation1446_fullAut1446To4362' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation4362_not_structuralFromFin_Equation1446_fullAut1446To4362._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 native_cell_correct._native.native_decide.ax_1_1,
 native_checked4362._native.native_decide.ax_1_1,
 native_orbit_correct._native.native_decide.ax_1_1,
 native_places_correct._native.native_decide.ax_1_1,
 native_probe_correct._native.native_decide.ax_1_1,
 native_sizes_correct._native.native_decide.ax_1_1,
 places_correct._native.native_decide.ax_1_1,
 sizes_pos._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4362_not_structuralFromFin_Equation1446_fullAut1446To4362

