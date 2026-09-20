import equational_theories.Definability.TransitiveInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianSetactionTuples3Choose2Symmetric

def genData : Array (Array (Fin 6)) := #[#[2, 3, 0, 1, 5, 4], #[1, 0, 4, 5, 2, 3]]
def gen (i : Fin 2) (x : Fin 6) : Fin 6 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 6)) := #[#[2, 3, 0, 1, 5, 4], #[1, 0, 4, 5, 2, 3]]
def genInv (i : Fin 2) (x : Fin 6) : Fin 6 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 6)) := #[]
def probe (i : Fin 0) (x : Fin 6) : Fin 6 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 6)) := #[]
def probeInv (i : Fin 0) (x : Fin 6) : Fin 6 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 6)) := #[#[0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5]]
def sourceRow (i : Fin 6) (x : Fin 6) : Fin 6 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 2) : Equiv.Perm (Fin 6) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 6) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 2)) := #[[], [0], [1], [1, 0], [0, 1], [0, 1, 0]]
def words (i : Fin 6) : List (Fin 2) := wordsData.getD i.val []
def repData : Array (Fin 6 × Fin 6) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 6)) := #[#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)], #[(1, 2), (0, 2), (4, 2), (5, 2), (2, 2), (3, 2)], #[(2, 1), (3, 1), (0, 1), (1, 1), (5, 1), (4, 1)], #[(4, 4), (5, 4), (1, 4), (0, 4), (3, 4), (2, 4)], #[(3, 3), (2, 3), (5, 3), (4, 3), (0, 3), (1, 3)], #[(5, 5), (4, 5), (3, 5), (2, 5), (1, 5), (0, 5)]]
def tr (x y : Fin 6) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![6, 6, 6, 6, 6, 6]
def valuesData : Array (Array (Fin 6)) := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 6 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 6)) := #[#[], #[], #[], #[], #[], #[]]
def stabilizers (i : Fin 6) (j : Fin 0) : Fin 6 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 6) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 6) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 6) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 6)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem same_orbit : ∀ i x y, (tr (genPerm i x) (genPerm i y)).1 = (tr x y).1 := by native_decide
theorem coherent_values : ∀ i x y a,
    genPerm i (wordPerm genPerm (words (tr x y).2) (values (tr x y).1 a)) =
    wordPerm genPerm (words (tr (genPerm i x) (genPerm i y)).2) (values (tr x y).1 a) := by native_decide

theorem family_generators : ∀ p i, (fam p).IsEndo (genPerm i) :=
  Magma.InvariantFamily.family_endos genPerm words tr sizes values same_orbit coherent_values

theorem tr_rep : ∀ i, tr (rep i).1 (rep i).2 = (i, 0) := by native_decide
theorem words_zero : words 0 = [] := by native_decide
theorem values_injective : ∀ i, Function.Injective (values i) := by native_decide

theorem op_rep (p : Params) (i) : (fam p).op (rep i).1 (rep i).2 = values i (p i) := by
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

theorem point_transitive : ∀ a,
    wordPerm genPerm (words (tr a a).2) 0 = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

private def law72 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count72 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law72} = 28 := by native_decide

private def law679 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0))))⟩
private theorem count679 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law679} = 15 := by native_decide

private def law872 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count872 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law872} = 15 := by native_decide

private def law916 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count916 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law916} = 34 := by native_decide

private def law1441 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count1441 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law1441} = 851 := by native_decide

private def law1518 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count1518 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law1518} = 21 := by native_decide

private def law1525 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count1525 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law1525} = 30 := by native_decide

private def law4269 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0)))⟩
private theorem count4269 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 6) (fam p) law4269} = 750 := by native_decide

end Magma.InvariantNonabelianSetactionTuples3Choose2Symmetric

open Magma.InvariantNonabelianSetactionTuples3Choose2Symmetric Magma.InvariantFamily

theorem Equation872_not_termStructuralFromFin_Equation1518_invariantFamilyCount : ¬ Law872.TermStructuralFromFin Law1518 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 6) (fam p) law1518) (fun p => PointTest (0 : Fin 6) (fam p) law872)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1518, count872]
    decide

/-- info: 'Equation872_not_termStructuralFromFin_Equation1518_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1518._native.native_decide.ax_1_1,
 count872._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation872_not_termStructuralFromFin_Equation1518_invariantFamilyCount

theorem Equation72_not_termStructuralFromFin_Equation916_invariantFamilyCount : ¬ Law72.TermStructuralFromFin Law916 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 6) (fam p) law916) (fun p => PointTest (0 : Fin 6) (fam p) law72)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count916, count72]
    decide

/-- info: 'Equation72_not_termStructuralFromFin_Equation916_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count72._native.native_decide.ax_1_1,
 count916._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation72_not_termStructuralFromFin_Equation916_invariantFamilyCount

theorem Equation1525_not_termStructuralFromFin_Equation916_invariantFamilyCount : ¬ Law1525.TermStructuralFromFin Law916 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 6) (fam p) law916) (fun p => PointTest (0 : Fin 6) (fam p) law1525)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count916, count1525]
    decide

/-- info: 'Equation1525_not_termStructuralFromFin_Equation916_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1525._native.native_decide.ax_1_1,
 count916._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1525_not_termStructuralFromFin_Equation916_invariantFamilyCount

theorem Equation4269_not_termStructuralFromFin_Equation1441_invariantFamilyCount : ¬ Law4269.TermStructuralFromFin Law1441 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 6) (fam p) law1441) (fun p => PointTest (0 : Fin 6) (fam p) law4269)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1441, count4269]
    decide

/-- info: 'Equation4269_not_termStructuralFromFin_Equation1441_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1441._native.native_decide.ax_1_1,
 count4269._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4269_not_termStructuralFromFin_Equation1441_invariantFamilyCount

theorem Equation679_not_termStructuralFromFin_Equation1518_invariantFamilyCount : ¬ Law679.TermStructuralFromFin Law1518 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 6) (fam p) law1518) (fun p => PointTest (0 : Fin 6) (fam p) law679)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1518, count679]
    decide

/-- info: 'Equation679_not_termStructuralFromFin_Equation1518_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 point_transitive._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1518._native.native_decide.ax_1_1,
 count679._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation679_not_termStructuralFromFin_Equation1518_invariantFamilyCount

