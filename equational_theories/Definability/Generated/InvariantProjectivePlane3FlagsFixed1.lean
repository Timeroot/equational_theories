import DefOrbit.Generated.NativeInvariantProjectivePlane3FlagsFixed1
import equational_theories.Definability.NativeOrbitCounting
import equational_theories.Definability.CachedWordImages
import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantProjectivePlane3FlagsFixed1

def genData : Array (Array (Fin 53)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.genData
def gen (i : Fin 12) (x : Fin 53) : Fin 53 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 53)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.genInvData
def genInv (i : Fin 12) (x : Fin 53) : Fin 53 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 53)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.probeData
def probe (i : Fin 0) (x : Fin 53) : Fin 53 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 53)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.probeInvData
def probeInv (i : Fin 0) (x : Fin 53) : Fin 53 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 53)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.sourceRowData
def sourceRow (i : Fin 53) (x : Fin 53) : Fin 53 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 12) : Equiv.Perm (Fin 53) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 53) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 12)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.wordsData
def words (i : Fin 1411) : List (Fin 12) := wordsData.getD i.val []
def repData : Array (Fin 53 × Fin 53) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.repData
def rep (i : Fin 9) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 9 × Fin 1411)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.trData
def tr (x y : Fin 53) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 9 → ℕ := ![2, 3, 7, 4, 4, 3, 2, 2, 1]
def valuesData : Array (Array (Fin 53)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.valuesData
def values (i : Fin 9) (j : Fin (sizes i)) : Fin 53 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 1411)) := DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.stabilizersData
def stabilizers (i : Fin 9) (j : Fin 2) : Fin 1411 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def paramEquiv : Params ≃ (Fin 84 × Fin 96) :=
  finPiFinEquiv.trans ((finCongr (by decide)).trans (finProdFinEquiv (m := 84) (n := 96)).symm)
def imageData : Array (Array (Fin 53)) :=
  wordImageData genPerm words
def image (i : Fin 1411) (x : Fin 53) : Fin 53 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 1411) (x : Fin 53) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 53) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 53) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 53)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem same_orbit : ∀ i x y, (tr (genPerm i x) (genPerm i y)).1 = (tr x y).1 := by native_decide
theorem coherent_values : ∀ i x y a,
    genPerm i (wordPerm genPerm (words (tr x y).2) (values (tr x y).1 a)) =
    wordPerm genPerm (words (tr (genPerm i x) (genPerm i y)).2) (values (tr x y).1 a) := by native_decide

theorem family_generators : ∀ p i, (fam p).IsEndo (genPerm i) := by
  intro p
  rw [fam_eq_family p]
  exact Magma.InvariantFamily.family_endos genPerm words tr sizes values same_orbit coherent_values p

theorem tr_rep : ∀ i, tr (rep i).1 (rep i).2 = (i, 0) := by native_decide
theorem words_zero : words 0 = [] := by native_decide
theorem values_injective : ∀ i, Function.Injective (values i) := by native_decide

private theorem abstract_op_rep {n g k m : Nat}
    (generators : Fin g → Equiv.Perm (Fin n)) (words : Fin k → List (Fin g))
    (rep : Fin m → Fin n × Fin n) (tr : Fin n → Fin n → Fin m × Fin k)
    (sizes : Fin m → Nat) (values : (i : Fin m) → Fin (sizes i) → Fin n)
    (zero : Fin k) (tr_rep : ∀ i, tr (rep i).1 (rep i).2 = (i, zero))
    (words_zero : words zero = []) (p : (i : Fin m) → Fin (sizes i)) (i : Fin m) :
    (family generators words tr sizes values p).op (rep i).1 (rep i).2 = values i (p i) := by
  change wordPerm generators (words (tr (rep i).1 (rep i).2).2)
    (values (tr (rep i).1 (rep i).2).1 (p (tr (rep i).1 (rep i).2).1)) = _
  rw [tr_rep]
  change wordPerm generators (words zero) (values i (p i)) = _
  rw [words_zero]
  rfl

theorem op_rep (p : Params) (i) : (fam p).op (rep i).1 (rep i).2 = values i (p i) := by
  have hf := congrArg (fun M : Magma (Fin 53) => M.op (rep i).1 (rep i).2) (fam_eq_family p)
  exact hf.trans (abstract_op_rep genPerm words rep tr sizes values 0 tr_rep words_zero p i)

theorem family_injective : Function.Injective (fun p : Params => (fam p).op) := by
  intro p q hpq
  funext i
  apply values_injective i
  rw [← op_rep p i, ← op_rep q i]
  exact congrFun (congrFun hpq (rep i).1) (rep i).2

def points : Fin 2 → Fin 53 := ![0, 52]
def point_index (x : Fin 53) : Fin 2 := if x.val < 52 then 0 else 1

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

def places : Fin 9 → ℕ := ![1, 2, 6, 42, 168, 672, 2016, 4032, 8064]
private theorem sizes_pos : ∀ j, 0 < sizes j := by native_decide
private theorem places_correct : ∀ j : Fin 9,
    places j = ∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k) := by native_decide
def decodeNative (i : Fin 84 × Fin 96) : Params := fun j =>
  ⟨((i.2.val + 96 * i.1.val) / places j) % sizes j, Nat.mod_lt _ (sizes_pos j)⟩
private theorem decodeNative_eq (i : Fin 84 × Fin 96) : decodeNative i = paramEquiv.symm i := by
  funext j
  apply Fin.ext
  change ((i.2.val + 96 * i.1.val) / places j) % sizes j =
    ((i.2.val + 96 * i.1.val) / (∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k))) % sizes j
  rw [places_correct]
private theorem native_orbit_correct : ∀ x y : Fin 53,
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.orbitData.getD (x.val * 53 + y.val) 0 = (tr x y).1.val := by native_decide
private theorem native_places_correct : ∀ j : Fin 9,
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.placesData.getD j.val 0 = places j := by native_decide
private theorem native_sizes_correct : ∀ j : Fin 9,
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.sizesData.getD j.val 0 = sizes j := by native_decide
private theorem native_cell_correct : ∀ (x y : Fin 53) (v : Fin (sizes (tr x y).1)),
    (DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.cellData.getD (x.val * 53 + y.val) #[]).getD v.val 0 =
      wordPerm genPerm (words (tr x y).2) (values (tr x y).1 v) := by native_decide
private theorem native_op_correct (i : Fin 84 × Fin 96) (x y : Fin 53) :
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.op (i.2.val + 96 * i.1.val) x y = (fam (paramEquiv.symm i)).op x y := by
  rw [← decodeNative_eq]
  unfold DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.op
  dsimp only
  rw [native_orbit_correct, native_places_correct, native_sizes_correct]
  exact (native_cell_correct x y (decodeNative i (tr x y).1)).trans (image_correct _ _).symm
private theorem native_point_correct : ∀ i : Fin 2,
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.point i = points i := by native_decide

private theorem native_cons3_2 {A : Type} (a : A) (p : Fin 2 → A) :
    (Fin.cons a p : Fin 3 → A) 2 = p 1 := by rfl

private def law824 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 2))))⟩
private theorem native_good824_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good824 code = true ↔ DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.test824 code := by
  simp [DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good824, DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.test824, List.all_eq_true]
private theorem abstract_test824 (M : Magma (Fin 53)) (ps : Fin 2 → Fin 53) :
    (∀ i : Fin 2, ∀ v0 v1 : Fin 53, (ps i) = (M.op (ps i) (M.op (M.op (ps i) v0) (M.op (ps i) v1)))) ↔
      Magma.InvariantFamily.OrbitTest ps M law824 := by
  simp only [Magma.InvariantFamily.OrbitTest, Magma.InvariantFamily.PointTest, law824,
    FreeMagma.evalInMagma, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_test824_correct (i : Fin 84 × Fin 96) :
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.test824 (i.2.val + 96 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law824 := by
  have hp : DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.point = points := funext native_point_correct
  have hm : (⟨DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.op (i.2.val + 96 * i.1.val)⟩ : Magma (Fin 53)) = fam (paramEquiv.symm i) :=
    congrArg Magma.mk (funext fun x => funext fun y => native_op_correct i x y)
  have h := abstract_test824 (⟨DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.op (i.2.val + 96 * i.1.val)⟩ : Magma (Fin 53)) DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.point
  apply h.trans
  rw [hp, hm]
private theorem native_count824 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good824 8064 = 80 := by native_decide
private theorem count824 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law824} = 80 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 84) (n := 96)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law824) DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good824]
  · exact native_count824
  · intro p
    have h := (native_test824_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good824_correct] using h

private def law1033 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 2))) (.Leaf 2)))⟩
private theorem native_good1033_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good1033 code = true ↔ DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.test1033 code := by
  simp [DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good1033, DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.test1033, List.all_eq_true]
private theorem abstract_test1033 (M : Magma (Fin 53)) (ps : Fin 2 → Fin 53) :
    (∀ i : Fin 2, ∀ v0 v1 : Fin 53, (ps i) = (M.op (ps i) (M.op (M.op (ps i) (M.op v0 v1)) v1))) ↔
      Magma.InvariantFamily.OrbitTest ps M law1033 := by
  simp only [Magma.InvariantFamily.OrbitTest, Magma.InvariantFamily.PointTest, law1033,
    FreeMagma.evalInMagma, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_test1033_correct (i : Fin 84 × Fin 96) :
    DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.test1033 (i.2.val + 96 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law1033 := by
  have hp : DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.point = points := funext native_point_correct
  have hm : (⟨DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.op (i.2.val + 96 * i.1.val)⟩ : Magma (Fin 53)) = fam (paramEquiv.symm i) :=
    congrArg Magma.mk (funext fun x => funext fun y => native_op_correct i x y)
  have h := abstract_test1033 (⟨DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.op (i.2.val + 96 * i.1.val)⟩ : Magma (Fin 53)) DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.point
  apply h.trans
  rw [hp, hm]
private theorem native_count1033 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good1033 8064 = 84 := by native_decide
private theorem count1033 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1033} = 84 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 84) (n := 96)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law1033) DefOrbit.NativeInvariantProjectivePlane3FlagsFixed1.good1033]
  · exact native_count1033
  · intro p
    have h := (native_test1033_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good1033_correct] using h

end Magma.InvariantProjectivePlane3FlagsFixed1

open Magma.InvariantProjectivePlane3FlagsFixed1 Magma.InvariantFamily

theorem Equation824_not_termStructuralFromFin_Equation1033_invariantFamilyCount : ¬ Law824.TermStructuralFromFin Law1033 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1033) (fun p => OrbitTest points (fam p) law824)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1033, count824]
    decide

/-- info: 'Equation824_not_termStructuralFromFin_Equation1033_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_cover._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 native_cell_correct._native.native_decide.ax_1_1,
 native_count1033._native.native_decide.ax_1_1,
 native_count824._native.native_decide.ax_1_1,
 native_orbit_correct._native.native_decide.ax_1_1,
 native_places_correct._native.native_decide.ax_1_1,
 native_point_correct._native.native_decide.ax_1_1,
 native_sizes_correct._native.native_decide.ax_1_1,
 places_correct._native.native_decide.ax_1_1,
 sizes_pos._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation824_not_termStructuralFromFin_Equation1033_invariantFamilyCount

