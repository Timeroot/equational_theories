import DefOrbit.Generated.NativeInvariantProjectiveLine5TriplesFixed1
import equational_theories.Definability.NativeOrbitCounting
import equational_theories.Definability.CachedWordImages
import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantProjectiveLine5TriplesFixed1

def genData : Array (Array (Fin 21)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.genData
def gen (i : Fin 6) (x : Fin 21) : Fin 21 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 21)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.genInvData
def genInv (i : Fin 6) (x : Fin 21) : Fin 21 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 21)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.probeData
def probe (i : Fin 0) (x : Fin 21) : Fin 21 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 21)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.probeInvData
def probeInv (i : Fin 0) (x : Fin 21) : Fin 21 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 21)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.sourceRowData
def sourceRow (i : Fin 21) (x : Fin 21) : Fin 21 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 6) : Equiv.Perm (Fin 21) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 21) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 6)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.wordsData
def words (i : Fin 120) : List (Fin 6) := wordsData.getD i.val []
def repData : Array (Fin 21 × Fin 21) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.repData
def rep (i : Fin 9) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 9 × Fin 120)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.trData
def tr (x y : Fin 21) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 9 → ℕ := ![3, 21, 5, 21, 5, 3, 3, 3, 1]
def valuesData : Array (Array (Fin 21)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.valuesData
def values (i : Fin 9) (j : Fin (sizes i)) : Fin 21 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 120)) := DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.stabilizersData
def stabilizers (i : Fin 9) (j : Fin 1) : Fin 120 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def paramEquiv : Params ≃ (Fin 945 × Fin 945) :=
  finPiFinEquiv.trans ((finCongr (by decide)).trans (finProdFinEquiv (m := 945) (n := 945)).symm)
def imageData : Array (Array (Fin 21)) :=
  wordImageData genPerm words
def image (i : Fin 120) (x : Fin 21) : Fin 21 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 120) (x : Fin 21) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 21) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 21) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 21)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
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

theorem op_rep (p : Params) (i) : (fam p).op (rep i).1 (rep i).2 = values i (p i) := by
  rw [fam_eq_family p]
  change wordPerm genPerm (words (tr (rep i).1 (rep i).2).2)
    (values (tr (rep i).1 (rep i).2).1 (p (tr (rep i).1 (rep i).2).1)) = _
  rw [tr_rep]
  change wordPerm genPerm (words 0) (values i (p i)) = _
  rw [words_zero]
  rfl

theorem family_injective : Function.Injective (fun p : Params => (fam p).op) := by
  intro p q hpq
  funext i
  apply values_injective i
  rw [← op_rep p i, ← op_rep q i]
  exact congrFun (congrFun hpq (rep i).1) (rep i).2

def points : Fin 2 → Fin 21 := ![0, 20]
def point_index (x : Fin 21) : Fin 2 := if x.val < 20 then 0 else 1

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

def places : Fin 9 → ℕ := ![1, 3, 63, 315, 6615, 33075, 99225, 297675, 893025]
private theorem sizes_pos : ∀ j, 0 < sizes j := by native_decide
private theorem places_correct : ∀ j : Fin 9,
    places j = ∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k) := by native_decide
def decodeNative (i : Fin 945 × Fin 945) : Params := fun j =>
  ⟨((i.2.val + 945 * i.1.val) / places j) % sizes j, Nat.mod_lt _ (sizes_pos j)⟩
private theorem decodeNative_eq (i : Fin 945 × Fin 945) : decodeNative i = paramEquiv.symm i := by
  funext j
  apply Fin.ext
  change ((i.2.val + 945 * i.1.val) / places j) % sizes j =
    ((i.2.val + 945 * i.1.val) / (∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k))) % sizes j
  rw [places_correct]
private theorem native_orbit_correct : ∀ x y : Fin 21,
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.orbitData.getD (x.val * 21 + y.val) 0 = (tr x y).1.val := by native_decide
private theorem native_places_correct : ∀ j : Fin 9,
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.placesData.getD j.val 0 = places j := by native_decide
private theorem native_sizes_correct : ∀ j : Fin 9,
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.sizesData.getD j.val 0 = sizes j := by native_decide
private theorem native_cell_correct : ∀ (x y : Fin 21) (v : Fin (sizes (tr x y).1)),
    (DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.cellData.getD (x.val * 21 + y.val) #[]).getD v.val 0 =
      wordPerm genPerm (words (tr x y).2) (values (tr x y).1 v) := by native_decide
private theorem native_op_correct (i : Fin 945 × Fin 945) (x y : Fin 21) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.op (i.2.val + 945 * i.1.val) x y = (fam (paramEquiv.symm i)).op x y := by
  rw [← decodeNative_eq]
  unfold DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.op
  dsimp only
  rw [native_orbit_correct, native_places_correct, native_sizes_correct]
  exact (native_cell_correct x y (decodeNative i (tr x y).1)).trans (image_correct _ _).symm
private theorem native_point_correct : ∀ i : Fin 2,
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.point i = points i := by native_decide

private theorem native_cons3_2 {A : Type} (a : A) (p : Fin 2 → A) :
    (Fin.cons a p : Fin 3 → A) 2 = p 1 := by rfl

private def law819 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem native_good819_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good819 code = true ↔ DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test819 code := by
  simp [DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good819, DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test819, List.all_eq_true]
private theorem native_test819_correct (i : Fin 945 × Fin 945) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test819 (i.2.val + 945 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law819 := by
  unfold DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test819 Magma.InvariantFamily.OrbitTest
    Magma.InvariantFamily.PointTest law819
  simp only [native_op_correct, native_point_correct, FreeMagma.evalInMagma,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_count819 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good819 893025 = 43477 := by native_decide
private theorem count819 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law819} = 43477 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 945) (n := 945)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law819) DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good819]
  · exact native_count819
  · intro p
    have h := (native_test819_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good819_correct] using h

private def law1050 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 1))) (.Leaf 2)))⟩
private theorem native_good1050_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1050 code = true ↔ DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1050 code := by
  simp [DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1050, DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1050, List.all_eq_true]
private theorem native_test1050_correct (i : Fin 945 × Fin 945) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1050 (i.2.val + 945 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law1050 := by
  unfold DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1050 Magma.InvariantFamily.OrbitTest
    Magma.InvariantFamily.PointTest law1050
  simp only [native_op_correct, native_point_correct, FreeMagma.evalInMagma,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_count1050 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1050 893025 = 11026 := by native_decide
private theorem count1050 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1050} = 11026 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 945) (n := 945)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law1050) DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1050]
  · exact native_count1050
  · intro p
    have h := (native_test1050_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good1050_correct] using h

private def law1253 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 1)) (.Leaf 2)))⟩
private theorem native_good1253_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1253 code = true ↔ DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1253 code := by
  simp [DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1253, DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1253, List.all_eq_true]
private theorem native_test1253_correct (i : Fin 945 × Fin 945) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1253 (i.2.val + 945 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law1253 := by
  unfold DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test1253 Magma.InvariantFamily.OrbitTest
    Magma.InvariantFamily.PointTest law1253
  simp only [native_op_correct, native_point_correct, FreeMagma.evalInMagma,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_count1253 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1253 893025 = 44101 := by native_decide
private theorem count1253 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1253} = 44101 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 945) (n := 945)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law1253) DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good1253]
  · exact native_count1253
  · intro p
    have h := (native_test1253_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good1253_correct] using h

private def law3259 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 1))))⟩
private theorem native_good3259_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good3259 code = true ↔ DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test3259 code := by
  simp [DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good3259, DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test3259, List.all_eq_true]
private theorem native_test3259_correct (i : Fin 945 × Fin 945) :
    DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test3259 (i.2.val + 945 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law3259 := by
  unfold DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.test3259 Magma.InvariantFamily.OrbitTest
    Magma.InvariantFamily.PointTest law3259
  simp only [native_op_correct, native_point_correct, FreeMagma.evalInMagma,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_count3259 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good3259 893025 = 6213 := by native_decide
private theorem count3259 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law3259} = 6213 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 945) (n := 945)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law3259) DefOrbit.NativeInvariantProjectiveLine5TriplesFixed1.good3259]
  · exact native_count3259
  · intro p
    have h := (native_test3259_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good3259_correct] using h

end Magma.InvariantProjectiveLine5TriplesFixed1

open Magma.InvariantProjectiveLine5TriplesFixed1 Magma.InvariantFamily

theorem Equation3259_not_termStructuralFromFin_Equation1050_invariantFamilyCount : ¬ Law3259.TermStructuralFromFin Law1050 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1050) (fun p => OrbitTest points (fam p) law3259)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1050, count3259]
    decide

#print axioms Equation3259_not_termStructuralFromFin_Equation1050_invariantFamilyCount

theorem Equation819_not_termStructuralFromFin_Equation1253_invariantFamilyCount : ¬ Law819.TermStructuralFromFin Law1253 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1253) (fun p => OrbitTest points (fam p) law819)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1253, count819]
    decide

#print axioms Equation819_not_termStructuralFromFin_Equation1253_invariantFamilyCount

