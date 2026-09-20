import DefOrbit.Generated.NativeInvariantProjectivePlane3Nonflags
import equational_theories.Definability.NativeOrbitCounting
import equational_theories.Definability.CachedWordImages
import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantProjectivePlane3Nonflags

def genData : Array (Array (Fin 117)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.genData
def gen (i : Fin 12) (x : Fin 117) : Fin 117 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 117)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.genInvData
def genInv (i : Fin 12) (x : Fin 117) : Fin 117 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 117)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.probeData
def probe (i : Fin 0) (x : Fin 117) : Fin 117 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 117)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.probeInvData
def probeInv (i : Fin 0) (x : Fin 117) : Fin 117 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 117)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.sourceRowData
def sourceRow (i : Fin 117) (x : Fin 117) : Fin 117 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 12) : Equiv.Perm (Fin 117) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 117) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 12)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.wordsData
def words (i : Fin 3463) : List (Fin 12) := wordsData.getD i.val []
def repData : Array (Fin 117 × Fin 117) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.repData
def rep (i : Fin 8) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 8 × Fin 3463)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.trData
def tr (x y : Fin 117) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 8 → ℕ := ![1, 3, 3, 13, 3, 13, 13, 9]
def valuesData : Array (Array (Fin 117)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.valuesData
def values (i : Fin 8) (j : Fin (sizes i)) : Fin 117 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 3463)) := DefOrbit.NativeInvariantProjectivePlane3Nonflags.stabilizersData
def stabilizers (i : Fin 8) (j : Fin 2) : Fin 3463 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 8) → Fin (sizes i)
def paramEquiv : Params ≃ (Fin 507 × Fin 1053) :=
  finPiFinEquiv.trans ((finCongr (by decide)).trans (finProdFinEquiv (m := 507) (n := 1053)).symm)
def imageData : Array (Array (Fin 117)) :=
  wordImageData genPerm words
def image (i : Fin 3463) (x : Fin 117) : Fin 117 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 3463) (x : Fin 117) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 117) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 117) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 117)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
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
  have hf := congrArg (fun M : Magma (Fin 117) => M.op (rep i).1 (rep i).2) (fam_eq_family p)
  exact hf.trans (abstract_op_rep genPerm words rep tr sizes values 0 tr_rep words_zero p i)

theorem family_injective : Function.Injective (fun p : Params => (fam p).op) := by
  intro p q hpq
  funext i
  apply values_injective i
  rw [← op_rep p i, ← op_rep q i]
  exact congrFun (congrFun hpq (rep i).1) (rep i).2

def points : Fin 1 → Fin 117 := ![0]
def point_index (x : Fin 117) : Fin 1 := 0

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

def places : Fin 8 → ℕ := ![1, 1, 3, 9, 117, 351, 4563, 59319]
private theorem sizes_pos : ∀ j, 0 < sizes j := by native_decide
private theorem places_correct : ∀ j : Fin 8,
    places j = ∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k) := by native_decide
def decodeNative (i : Fin 507 × Fin 1053) : Params := fun j =>
  ⟨((i.2.val + 1053 * i.1.val) / places j) % sizes j, Nat.mod_lt _ (sizes_pos j)⟩
private theorem decodeNative_eq (i : Fin 507 × Fin 1053) : decodeNative i = paramEquiv.symm i := by
  funext j
  apply Fin.ext
  change ((i.2.val + 1053 * i.1.val) / places j) % sizes j =
    ((i.2.val + 1053 * i.1.val) / (∏ k : Fin j.val, sizes (Fin.castLE j.isLt.le k))) % sizes j
  rw [places_correct]
private theorem native_orbit_correct : ∀ x y : Fin 117,
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.orbitData.getD (x.val * 117 + y.val) 0 = (tr x y).1.val := by native_decide
private theorem native_places_correct : ∀ j : Fin 8,
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.placesData.getD j.val 0 = places j := by native_decide
private theorem native_sizes_correct : ∀ j : Fin 8,
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.sizesData.getD j.val 0 = sizes j := by native_decide
private theorem native_cell_correct : ∀ (x y : Fin 117) (v : Fin (sizes (tr x y).1)),
    (DefOrbit.NativeInvariantProjectivePlane3Nonflags.cellData.getD (x.val * 117 + y.val) #[]).getD v.val 0 =
      wordPerm genPerm (words (tr x y).2) (values (tr x y).1 v) := by native_decide
private theorem native_op_correct (i : Fin 507 × Fin 1053) (x y : Fin 117) :
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.op (i.2.val + 1053 * i.1.val) x y = (fam (paramEquiv.symm i)).op x y := by
  rw [← decodeNative_eq]
  unfold DefOrbit.NativeInvariantProjectivePlane3Nonflags.op
  dsimp only
  rw [native_orbit_correct, native_places_correct, native_sizes_correct]
  exact (native_cell_correct x y (decodeNative i (tr x y).1)).trans (image_correct _ _).symm
private theorem native_point_correct : ∀ i : Fin 1,
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.point i = points i := by native_decide

private theorem native_cons3_2 {A : Type} (a : A) (p : Fin 2 → A) :
    (Fin.cons a p : Fin 3 → A) 2 = p 1 := by rfl

private def law1233 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 1)) (.Leaf 2)))⟩
private theorem native_good1233_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1233 code = true ↔ DefOrbit.NativeInvariantProjectivePlane3Nonflags.test1233 code := by
  simp [DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1233, DefOrbit.NativeInvariantProjectivePlane3Nonflags.test1233, List.all_eq_true]
private theorem abstract_test1233 (M : Magma (Fin 117)) (ps : Fin 1 → Fin 117) :
    (∀ i : Fin 1, ∀ v0 v1 : Fin 117, (ps i) = (M.op (ps i) (M.op (M.op (M.op (ps i) v0) v0) v1))) ↔
      Magma.InvariantFamily.OrbitTest ps M law1233 := by
  simp only [Magma.InvariantFamily.OrbitTest, Magma.InvariantFamily.PointTest, law1233,
    FreeMagma.evalInMagma, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_test1233_correct (i : Fin 507 × Fin 1053) :
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.test1233 (i.2.val + 1053 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law1233 := by
  have hp : DefOrbit.NativeInvariantProjectivePlane3Nonflags.point = points := funext native_point_correct
  have hm : (⟨DefOrbit.NativeInvariantProjectivePlane3Nonflags.op (i.2.val + 1053 * i.1.val)⟩ : Magma (Fin 117)) = fam (paramEquiv.symm i) :=
    congrArg Magma.mk (funext fun x => funext fun y => native_op_correct i x y)
  have h := abstract_test1233 (⟨DefOrbit.NativeInvariantProjectivePlane3Nonflags.op (i.2.val + 1053 * i.1.val)⟩ : Magma (Fin 117)) DefOrbit.NativeInvariantProjectivePlane3Nonflags.point
  apply h.trans
  rw [hp, hm]
private theorem native_count1233 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1233 533871 = 199 := by native_decide
private theorem count1233 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1233} = 199 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 507) (n := 1053)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law1233) DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1233]
  · exact native_count1233
  · intro p
    have h := (native_test1233_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good1233_correct] using h

private def law1236 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 2)) (.Leaf 2)))⟩
private theorem native_good1236_correct (code : Nat) :
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1236 code = true ↔ DefOrbit.NativeInvariantProjectivePlane3Nonflags.test1236 code := by
  simp [DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1236, DefOrbit.NativeInvariantProjectivePlane3Nonflags.test1236, List.all_eq_true]
private theorem abstract_test1236 (M : Magma (Fin 117)) (ps : Fin 1 → Fin 117) :
    (∀ i : Fin 1, ∀ v0 v1 : Fin 117, (ps i) = (M.op (ps i) (M.op (M.op (M.op (ps i) v0) v1) v1))) ↔
      Magma.InvariantFamily.OrbitTest ps M law1236 := by
  simp only [Magma.InvariantFamily.OrbitTest, Magma.InvariantFamily.PointTest, law1236,
    FreeMagma.evalInMagma, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one, native_cons3_2]
private theorem native_test1236_correct (i : Fin 507 × Fin 1053) :
    DefOrbit.NativeInvariantProjectivePlane3Nonflags.test1236 (i.2.val + 1053 * i.1.val) ↔
      Magma.InvariantFamily.OrbitTest points (fam (paramEquiv.symm i)) law1236 := by
  have hp : DefOrbit.NativeInvariantProjectivePlane3Nonflags.point = points := funext native_point_correct
  have hm : (⟨DefOrbit.NativeInvariantProjectivePlane3Nonflags.op (i.2.val + 1053 * i.1.val)⟩ : Magma (Fin 117)) = fam (paramEquiv.symm i) :=
    congrArg Magma.mk (funext fun x => funext fun y => native_op_correct i x y)
  have h := abstract_test1236 (⟨DefOrbit.NativeInvariantProjectivePlane3Nonflags.op (i.2.val + 1053 * i.1.val)⟩ : Magma (Fin 117)) DefOrbit.NativeInvariantProjectivePlane3Nonflags.point
  apply h.trans
  rw [hp, hm]
private theorem native_count1236 :
    DefOrbit.countBelow DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1236 533871 = 195 := by native_decide
private theorem count1236 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1236} = 195 := by
  rw [DefOrbit.card_eq_countBelow
    (paramEquiv.trans (finProdFinEquiv (m := 507) (n := 1053)))
    (fun p => Magma.InvariantFamily.OrbitTest points (fam p) law1236) DefOrbit.NativeInvariantProjectivePlane3Nonflags.good1236]
  · exact native_count1236
  · intro p
    have h := (native_test1236_correct (paramEquiv p)).symm
    simpa only [Equiv.symm_apply_apply, native_good1236_correct] using h

end Magma.InvariantProjectivePlane3Nonflags

open Magma.InvariantProjectivePlane3Nonflags Magma.InvariantFamily

theorem Equation1236_not_termStructuralFromFin_Equation1233_invariantFamilyCount : ¬ Law1236.TermStructuralFromFin Law1233 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1233) (fun p => OrbitTest points (fam p) law1236)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1233, count1236]
    decide

#print axioms Equation1236_not_termStructuralFromFin_Equation1233_invariantFamilyCount

