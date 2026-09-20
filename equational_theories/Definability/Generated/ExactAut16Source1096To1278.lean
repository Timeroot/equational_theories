import DefOrbit.Generated.NativeExactAut16Source1096To1278
import equational_theories.Definability.NativeOrbit

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ExactAut16Source1096To1278

def genData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 12, 13, 15, 14, 8, 9, 11, 10, 4, 5, 7, 6], #[0, 1, 6, 7, 12, 13, 2, 3, 8, 9, 14, 15, 4, 5, 10, 11], #[1, 0, 2, 3, 13, 12, 14, 15, 9, 8, 10, 11, 5, 4, 6, 7], #[2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5]]
def gen (i : Fin 4) (x : Fin 16) : Fin 16 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 16)) := #[#[0, 1, 3, 2, 12, 13, 15, 14, 8, 9, 11, 10, 4, 5, 7, 6], #[0, 1, 6, 7, 12, 13, 2, 3, 8, 9, 14, 15, 4, 5, 10, 11], #[1, 0, 2, 3, 13, 12, 14, 15, 9, 8, 10, 11, 5, 4, 6, 7], #[2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5]]
def genInv (i : Fin 4) (x : Fin 16) : Fin 16 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 16)) := #[#[0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13, 6, 7]]
def probe (i : Fin 1) (x : Fin 16) : Fin 16 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 16)) := #[#[0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13, 6, 7]]
def probeInv (i : Fin 1) (x : Fin 16) : Fin 16 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 16)) := #[#[1, 0, 6, 15, 5, 4, 2, 11, 9, 8, 14, 7, 13, 12, 10, 3], #[1, 0, 14, 7, 5, 4, 10, 3, 9, 8, 6, 15, 13, 12, 2, 11], #[12, 5, 3, 2, 8, 1, 7, 6, 4, 13, 11, 10, 0, 9, 15, 14], #[4, 13, 3, 2, 0, 9, 7, 6, 12, 5, 11, 10, 8, 1, 15, 14], #[1, 0, 14, 7, 5, 4, 10, 3, 9, 8, 6, 15, 13, 12, 2, 11], #[1, 0, 6, 15, 5, 4, 2, 11, 9, 8, 14, 7, 13, 12, 10, 3], #[4, 13, 3, 2, 0, 9, 7, 6, 12, 5, 11, 10, 8, 1, 15, 14], #[12, 5, 3, 2, 8, 1, 7, 6, 4, 13, 11, 10, 0, 9, 15, 14], #[1, 0, 6, 15, 5, 4, 2, 11, 9, 8, 14, 7, 13, 12, 10, 3], #[1, 0, 14, 7, 5, 4, 10, 3, 9, 8, 6, 15, 13, 12, 2, 11], #[12, 5, 3, 2, 8, 1, 7, 6, 4, 13, 11, 10, 0, 9, 15, 14], #[4, 13, 3, 2, 0, 9, 7, 6, 12, 5, 11, 10, 8, 1, 15, 14], #[1, 0, 14, 7, 5, 4, 10, 3, 9, 8, 6, 15, 13, 12, 2, 11], #[1, 0, 6, 15, 5, 4, 2, 11, 9, 8, 14, 7, 13, 12, 10, 3], #[4, 13, 3, 2, 0, 9, 7, 6, 12, 5, 11, 10, 8, 1, 15, 14], #[12, 5, 3, 2, 8, 1, 7, 6, 4, 13, 11, 10, 0, 9, 15, 14]]
def sourceRow (i : Fin 16) (x : Fin 16) : Fin 16 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 16) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 16) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [2], [3], [3, 2], [1, 3], [1, 3, 2], [0, 1, 3], [2, 1, 3], [3, 1, 3], [3, 1, 3, 2], [1, 0, 1, 3], [3, 0, 1, 3], [1, 2, 1, 3], [3, 2, 1, 3], [3, 1, 0, 1, 3], [3, 1, 2, 1, 3], [2, 3, 1, 3, 1, 3, 0, 1, 3], [0], [1, 0], [2, 0], [3, 0], [0, 1], [2, 1], [3, 1], [1, 2], [0, 1, 0], [2, 1, 0], [3, 1, 0], [1, 2, 0], [3, 2, 0], [1, 3, 0], [1, 0, 1], [3, 0, 1], [1, 2, 1], [3, 2, 1], [1, 3, 1], [3, 1, 2], [1, 0, 1, 0], [3, 0, 1, 0], [1, 2, 1, 0], [3, 2, 1, 0], [1, 3, 1, 0], [3, 1, 2, 0], [1, 3, 2, 0], [0, 1, 3, 0], [2, 1, 3, 0], [3, 1, 3, 0], [3, 1, 0, 1], [1, 3, 0, 1], [3, 1, 2, 1], [1, 3, 2, 1], [0, 1, 3, 1], [2, 1, 3, 1], [3, 1, 3, 1], [1, 3, 1, 2], [1, 3, 1, 3], [3, 1, 0, 1, 0], [1, 3, 0, 1, 0], [3, 1, 2, 1, 0], [1, 3, 2, 1, 0], [0, 1, 3, 1, 0], [2, 1, 3, 1, 0], [3, 1, 3, 1, 0], [1, 3, 1, 2, 0], [3, 1, 3, 2, 0], [1, 0, 1, 3, 0], [3, 0, 1, 3, 0], [1, 2, 1, 3, 0], [3, 2, 1, 3, 0], [1, 3, 1, 3, 0], [1, 3, 1, 0, 1], [0, 1, 3, 0, 1], [2, 1, 3, 0, 1], [3, 1, 3, 0, 1], [1, 3, 1, 2, 1], [3, 1, 3, 2, 1], [1, 0, 1, 3, 1], [3, 0, 1, 3, 1], [1, 2, 1, 3, 1], [1, 3, 1, 3, 1], [3, 1, 3, 1, 2], [1, 3, 1, 0, 1, 0], [0, 1, 3, 0, 1, 0], [2, 1, 3, 0, 1, 0], [3, 1, 3, 0, 1, 0], [1, 3, 1, 2, 1, 0], [3, 1, 3, 2, 1, 0], [1, 0, 1, 3, 1, 0], [3, 0, 1, 3, 1, 0], [1, 2, 1, 3, 1, 0], [1, 3, 1, 3, 1, 0], [3, 1, 3, 1, 2, 0], [3, 1, 0, 1, 3, 0], [3, 1, 2, 1, 3, 0], [0, 1, 3, 1, 0, 1], [2, 1, 3, 1, 0, 1], [3, 1, 3, 1, 0, 1], [1, 0, 1, 3, 0, 1], [3, 0, 1, 3, 0, 1], [1, 2, 1, 3, 0, 1], [3, 2, 1, 3, 0, 1], [3, 1, 3, 1, 2, 1], [3, 1, 0, 1, 3, 1], [3, 1, 2, 1, 3, 1], [1, 3, 1, 3, 1, 2], [1, 3, 1, 0, 1, 3], [1, 3, 1, 2, 1, 3], [0, 1, 3, 1, 0, 1, 0], [2, 1, 3, 1, 0, 1, 0], [3, 1, 3, 1, 0, 1, 0], [1, 0, 1, 3, 0, 1, 0], [3, 0, 1, 3, 0, 1, 0], [1, 2, 1, 3, 0, 1, 0], [3, 2, 1, 3, 0, 1, 0], [3, 1, 3, 1, 2, 1, 0], [3, 1, 0, 1, 3, 1, 0], [3, 1, 2, 1, 3, 1, 0], [1, 3, 1, 3, 1, 2, 0], [1, 3, 1, 0, 1, 3, 0], [1, 3, 1, 2, 1, 3, 0], [1, 0, 1, 3, 1, 0, 1], [1, 2, 1, 3, 1, 0, 1], [1, 3, 1, 0, 1, 3, 1], [1, 3, 1, 2, 1, 3, 1], [1, 0, 1, 3, 1, 0, 1, 0], [1, 2, 1, 3, 1, 0, 1, 0], [1, 3, 1, 0, 1, 3, 1, 0], [1, 3, 1, 2, 1, 3, 1, 0]]
def words (i : Fin 128) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 16 × Fin 16) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 8), (0, 9)]
def rep (i : Fin 7) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 7 × Fin 128)) := #[#[(0, 0), (1, 0), (2, 0), (2, 17), (3, 0), (4, 0), (2, 16), (2, 18), (5, 0), (6, 0), (2, 37), (2, 31), (3, 17), (4, 17), (2, 25), (2, 21)], #[(1, 1), (0, 1), (2, 1), (2, 19), (4, 19), (3, 19), (2, 24), (2, 28), (6, 1), (5, 1), (2, 33), (2, 39), (4, 1), (3, 1), (2, 22), (2, 26)], #[(2, 2), (2, 20), (0, 2), (1, 2), (2, 38), (2, 32), (3, 20), (4, 20), (2, 56), (2, 47), (5, 2), (6, 2), (2, 23), (2, 27), (3, 2), (4, 2)], #[(2, 3), (2, 29), (1, 3), (0, 3), (2, 34), (2, 40), (4, 3), (3, 3), (2, 49), (2, 58), (6, 3), (5, 3), (2, 36), (2, 42), (4, 29), (3, 29)], #[(3, 68), (4, 68), (2, 68), (2, 13), (0, 13), (1, 13), (2, 55), (2, 69), (3, 13), (4, 13), (2, 79), (2, 90), (5, 13), (6, 13), (2, 100), (2, 113)], #[(4, 66), (3, 66), (2, 11), (2, 66), (1, 11), (0, 11), (2, 77), (2, 88), (4, 11), (3, 11), (2, 104), (2, 117), (6, 11), (5, 11), (2, 111), (2, 98)], #[(2, 4), (2, 30), (3, 30), (4, 30), (2, 35), (2, 41), (0, 4), (1, 4), (2, 81), (2, 70), (3, 4), (4, 4), (2, 57), (2, 48), (5, 4), (6, 4)], #[(2, 5), (2, 43), (4, 5), (3, 5), (2, 54), (2, 63), (1, 5), (0, 5), (2, 74), (2, 85), (4, 43), (3, 43), (2, 50), (2, 59), (6, 5), (5, 5)], #[(5, 15), (6, 15), (2, 93), (2, 15), (3, 15), (4, 15), (2, 119), (2, 106), (0, 15), (1, 15), (2, 127), (2, 123), (3, 93), (4, 93), (2, 116), (2, 103)], #[(6, 14), (5, 14), (2, 14), (2, 92), (4, 14), (3, 14), (2, 105), (2, 118), (1, 14), (0, 14), (2, 122), (2, 126), (4, 92), (3, 92), (2, 102), (2, 115)], #[(2, 67), (2, 12), (5, 12), (6, 12), (2, 89), (2, 78), (3, 67), (4, 67), (2, 121), (2, 125), (0, 12), (1, 12), (2, 99), (2, 112), (3, 12), (4, 12)], #[(2, 10), (2, 65), (6, 10), (5, 10), (2, 76), (2, 87), (4, 65), (3, 65), (2, 124), (2, 120), (1, 10), (0, 10), (2, 110), (2, 97), (4, 10), (3, 10)], #[(3, 46), (4, 46), (2, 8), (2, 46), (5, 8), (6, 8), (2, 84), (2, 73), (3, 8), (4, 8), (2, 109), (2, 96), (0, 8), (1, 8), (2, 53), (2, 62)], #[(4, 9), (3, 9), (2, 9), (2, 64), (6, 9), (5, 9), (2, 75), (2, 86), (4, 64), (3, 64), (2, 101), (2, 114), (1, 9), (0, 9), (2, 80), (2, 91)], #[(2, 45), (2, 7), (3, 45), (4, 45), (2, 72), (2, 83), (5, 7), (6, 7), (2, 95), (2, 108), (3, 7), (4, 7), (2, 61), (2, 52), (0, 7), (1, 7)], #[(2, 6), (2, 44), (4, 44), (3, 44), (2, 82), (2, 71), (6, 6), (5, 6), (2, 107), (2, 94), (4, 6), (3, 6), (2, 51), (2, 60), (1, 6), (0, 6)]]
def tr (x y : Fin 16) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 7 → ℕ := ![4, 4, 16, 8, 8, 4, 4]
def valuesData : Array (Array (Fin 16)) := #[#[0, 1, 8, 9], #[0, 1, 8, 9], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 4, 5, 8, 9, 12, 13], #[0, 1, 4, 5, 8, 9, 12, 13], #[0, 1, 8, 9], #[0, 1, 8, 9]]
def values (i : Fin 7) (j : Fin (sizes i)) : Fin 16 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 128)) := #[#[16], #[16], #[0], #[21], #[21], #[16], #[16]]
def stabilizers (i : Fin 7) (j : Fin 1) : Fin 128 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 7) → Fin (sizes i)
def paramEquiv : Params ≃ (Fin 512 × Fin 512) :=
  finPiFinEquiv.trans ((finCongr (by decide)).trans (finProdFinEquiv (m := 512) (n := 512)).symm)
def imageData : Array (Array (Fin 16)) :=
  wordImageData genPerm words
def image (i : Fin 128) (x : Fin 16) : Fin 16 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 128) (x : Fin 16) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 16) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 16) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 16)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

def places : Fin 7 → ℕ := ![1, 4, 16, 256, 2048, 16384, 65536]
private theorem sizes_pos : ∀ j, 0 < sizes j := by native_decide
private theorem places_correct : ∀ j : Fin 7,
    places j = ∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k) := by native_decide
def decodeNative (i : Fin 512 × Fin 512) : Params := fun j =>
  ⟨((i.2.val + 512 * i.1.val) / places j) % sizes j, Nat.mod_lt _ (sizes_pos j)⟩
private theorem decodeNative_eq (i : Fin 512 × Fin 512) : decodeNative i = paramEquiv.symm i := by
  funext j
  apply Fin.ext
  change ((i.2.val + 512 * i.1.val) / places j) % sizes j =
    ((i.2.val + 512 * i.1.val) / (∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k))) % sizes j
  rw [places_correct]
private theorem native_orbit_correct : ∀ x y : Fin 16,
    DefOrbit.NativeExactAut16Source1096To1278.orbitData.getD (x.val * 16 + y.val) 0 = (tr x y).1.val := by native_decide
private theorem native_places_correct : ∀ j : Fin 7,
    DefOrbit.NativeExactAut16Source1096To1278.placesData.getD j.val 0 = places j := by native_decide
private theorem native_sizes_correct : ∀ j : Fin 7,
    DefOrbit.NativeExactAut16Source1096To1278.sizesData.getD j.val 0 = sizes j := by native_decide
private theorem native_cell_correct : ∀ (x y : Fin 16) (v : Fin (sizes (tr x y).1)),
    (DefOrbit.NativeExactAut16Source1096To1278.cellData.getD (x.val * 16 + y.val) #[]).getD v.val 0 =
      image (tr x y).2 (values (tr x y).1 v) := by native_decide
private theorem native_op_correct (i : Fin 512 × Fin 512) (x y : Fin 16) :
    DefOrbit.NativeExactAut16Source1096To1278.op (i.2.val + 512 * i.1.val) x y = (fam (paramEquiv.symm i)).op x y := by
  rw [← decodeNative_eq]
  unfold DefOrbit.NativeExactAut16Source1096To1278.op
  dsimp only
  rw [native_orbit_correct, native_places_correct, native_sizes_correct]
  exact native_cell_correct x y (decodeNative i (tr x y).1)
private theorem native_probe_correct : ∀ i : Fin 1, ∀ x : Fin 16,
    DefOrbit.NativeExactAut16Source1096To1278.probe i x = probePerm i x := by native_decide
private theorem native_pattern_correct (i : Fin 512 × Fin 512) :
    DefOrbit.NativeExactAut16Source1096To1278.pattern (i.2.val + 512 * i.1.val) ↔ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by
  unfold DefOrbit.NativeExactAut16Source1096To1278.pattern Pattern pattern
  simp only [native_op_correct, native_probe_correct, Magma.IsEndo]
  simp

private abbrev test1278 (p : Params) : Prop := ∀ y : Fin 16, 0 = ((fam p).op y ((fam p).op ((fam p).op ((fam p).op 0 0) y) 0))
private theorem native_test1278_correct (i : Fin 512 × Fin 512) :
    DefOrbit.NativeExactAut16Source1096To1278.test1278 (i.2.val + 512 * i.1.val) ↔ test1278 (paramEquiv.symm i) := by
  unfold DefOrbit.NativeExactAut16Source1096To1278.test1278 test1278
  simp only [native_op_correct]
private theorem native_checked1278 : DefOrbit.allBelow DefOrbit.NativeExactAut16Source1096To1278.check1278 262144 = true := by
  native_decide
private theorem restricted1278 : ∀ p : Params, test1278 p → ¬ Pattern (fam p) probePerm pattern := by
  have h : ∀ i : Fin 512 × Fin 512, test1278 (paramEquiv.symm i) →
      ¬ Pattern (fam (paramEquiv.symm i)) probePerm pattern := by
    intro i
    have hi : i.2.val + 512 * i.1.val < 262144 := by omega
    have hc := (DefOrbit.allBelow_spec _ _).mp native_checked1278 _ hi
    have ht := of_decide_eq_true hc
    change DefOrbit.NativeExactAut16Source1096To1278.test1278 (i.2.val + 512 * i.1.val) → ¬ DefOrbit.NativeExactAut16Source1096To1278.pattern (i.2.val + 512 * i.1.val) at ht
    simpa only [native_test1278_correct, native_pattern_correct] using ht
  intro p
  simpa only [Equiv.symm_apply_apply] using h (paramEquiv p)
theorem target1278 : ∀ p : Params, @Equation1278 (Fin 16) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted1278 p (ht 0)

end Magma.ExactAut16Source1096To1278

open Magma.ExactAut16Source1096To1278

theorem Equation1278_not_structuralFromFin_Equation1096_exactAut16Source1096To1278 : ¬ Law1278.StructuralFromFin Law1096 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1096.models_iff (Fin 16) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1278 p ((@Law1278.models_iff (Fin 16) (fam p)).mp hp)

/-- info: 'Equation1278_not_structuralFromFin_Equation1096_exactAut16Source1096To1278' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1278_not_structuralFromFin_Equation1096_exactAut16Source1096To1278._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 native_cell_correct._native.native_decide.ax_1_1,
 native_checked1278._native.native_decide.ax_1_1,
 native_orbit_correct._native.native_decide.ax_1_1,
 native_places_correct._native.native_decide.ax_1_1,
 native_probe_correct._native.native_decide.ax_1_1,
 native_sizes_correct._native.native_decide.ax_1_1,
 places_correct._native.native_decide.ax_1_1,
 sizes_pos._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1278_not_structuralFromFin_Equation1096_exactAut16Source1096To1278

