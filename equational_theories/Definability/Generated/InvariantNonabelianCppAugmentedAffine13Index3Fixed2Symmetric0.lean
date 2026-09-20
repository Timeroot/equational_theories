import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianCppAugmentedAffine13Index3Fixed2Symmetric0

def genData : Array (Array (Fin 15)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14], #[0, 8, 3, 11, 6, 1, 9, 4, 12, 7, 2, 10, 5, 13, 14], #[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14], #[0, 5, 10, 2, 7, 12, 4, 9, 1, 6, 11, 3, 8, 13, 14]]
def gen (i : Fin 4) (x : Fin 15) : Fin 15 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 15)) := #[#[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14], #[0, 5, 10, 2, 7, 12, 4, 9, 1, 6, 11, 3, 8, 13, 14], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14], #[0, 8, 3, 11, 6, 1, 9, 4, 12, 7, 2, 10, 5, 13, 14]]
def genInv (i : Fin 4) (x : Fin 15) : Fin 15 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 15)) := #[]
def probe (i : Fin 0) (x : Fin 15) : Fin 15 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 15)) := #[]
def probeInv (i : Fin 0) (x : Fin 15) : Fin 15 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 15)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13], #[14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14]]
def sourceRow (i : Fin 15) (x : Fin 15) : Fin 15 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 15) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 15) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [2], [0, 0], [1, 0], [3, 0], [2, 2], [0, 0, 0], [3, 0, 0], [0, 1, 0], [2, 1, 0], [0, 3, 0], [2, 3, 0], [2, 3, 0, 3, 2, 3, 0], [3], [0, 1], [1, 1], [2, 1], [1, 2], [3, 2], [0, 3], [2, 3], [1, 0, 0], [1, 1, 0], [0, 0, 1], [1, 0, 1], [3, 0, 1], [0, 1, 1], [1, 2, 1], [2, 2, 1], [3, 2, 1], [0, 1, 2], [2, 1, 2], [1, 2, 2], [2, 2, 2], [3, 2, 2], [0, 3, 2], [2, 3, 2], [0, 0, 3], [2, 2, 3], [0, 0, 0, 0], [1, 1, 0, 0], [1, 0, 1, 0], [3, 0, 1, 0], [1, 2, 1, 0], [3, 2, 1, 0], [1, 0, 0, 1], [0, 1, 0, 1], [0, 0, 1, 1], [0, 1, 2, 1], [1, 2, 2, 1], [2, 3, 2, 1]]
def words (i : Fin 52) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 15 × Fin 15) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 13), (0, 14), (13, 0), (13, 13), (13, 14), (14, 0), (14, 13), (14, 14)]
def rep (i : Fin 12) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 12 × Fin 52)) := #[#[(0, 0), (1, 0), (2, 0), (2, 13), (3, 0), (1, 14), (3, 13), (3, 14), (1, 13), (3, 16), (2, 14), (2, 16), (1, 16), (4, 0), (5, 0)], #[(1, 27), (0, 1), (1, 1), (2, 1), (2, 15), (3, 1), (1, 20), (3, 15), (3, 20), (1, 15), (3, 27), (2, 20), (2, 27), (4, 1), (5, 1)], #[(2, 48), (1, 48), (0, 3), (1, 3), (2, 3), (2, 24), (3, 3), (1, 38), (3, 24), (3, 38), (1, 24), (3, 48), (2, 38), (4, 3), (5, 3)], #[(2, 35), (2, 46), (1, 46), (0, 7), (1, 7), (2, 7), (2, 22), (3, 7), (1, 35), (3, 22), (3, 35), (1, 22), (3, 46), (4, 7), (5, 7)], #[(3, 44), (2, 12), (2, 44), (1, 44), (0, 12), (1, 40), (2, 40), (2, 32), (3, 40), (1, 12), (3, 32), (3, 12), (1, 32), (4, 12), (5, 12)], #[(1, 18), (3, 28), (2, 5), (2, 28), (1, 28), (0, 5), (1, 26), (2, 26), (2, 18), (3, 26), (1, 5), (3, 18), (3, 5), (4, 5), (5, 5)], #[(3, 11), (1, 31), (3, 49), (2, 11), (2, 49), (1, 49), (0, 11), (1, 43), (2, 43), (2, 31), (3, 43), (1, 11), (3, 31), (4, 11), (5, 11)], #[(3, 10), (3, 37), (1, 10), (3, 42), (2, 37), (2, 42), (1, 42), (0, 10), (1, 51), (2, 51), (2, 10), (3, 51), (1, 37), (4, 10), (5, 10)], #[(1, 19), (3, 4), (3, 19), (1, 4), (3, 25), (2, 19), (2, 25), (1, 25), (0, 4), (1, 30), (2, 30), (2, 4), (3, 30), (4, 4), (5, 4)], #[(3, 45), (1, 36), (3, 9), (3, 36), (1, 9), (3, 47), (2, 36), (2, 47), (1, 47), (0, 9), (1, 45), (2, 45), (2, 9), (4, 9), (5, 9)], #[(2, 33), (3, 34), (1, 8), (3, 33), (3, 8), (1, 33), (3, 50), (2, 8), (2, 50), (1, 50), (0, 8), (1, 34), (2, 34), (4, 8), (5, 8)], #[(2, 6), (2, 29), (3, 6), (1, 39), (3, 29), (3, 39), (1, 29), (3, 41), (2, 39), (2, 41), (1, 41), (0, 6), (1, 6), (4, 6), (5, 6)], #[(1, 2), (2, 2), (2, 17), (3, 2), (1, 21), (3, 17), (3, 21), (1, 17), (3, 23), (2, 21), (2, 23), (1, 23), (0, 2), (4, 2), (5, 2)], #[(6, 0), (6, 1), (6, 3), (6, 7), (6, 12), (6, 5), (6, 11), (6, 10), (6, 4), (6, 9), (6, 8), (6, 6), (6, 2), (7, 0), (8, 0)], #[(9, 0), (9, 1), (9, 3), (9, 7), (9, 12), (9, 5), (9, 11), (9, 10), (9, 4), (9, 9), (9, 8), (9, 6), (9, 2), (10, 0), (11, 0)]]
def tr (x y : Fin 15) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 12 → ℕ := ![3, 15, 15, 15, 3, 3, 3, 2, 2, 3, 2, 2]
def valuesData : Array (Array (Fin 15)) := #[#[0, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 13, 14], #[0, 13, 14], #[0, 13, 14], #[13, 14], #[13, 14], #[0, 13, 14], #[13, 14], #[13, 14]]
def values (i : Fin 12) (j : Fin (sizes i)) : Fin 15 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 52)) := #[#[13], #[0], #[0], #[0], #[13], #[13], #[13], #[1], #[1], #[13], #[1], #[1]]
def stabilizers (i : Fin 12) (j : Fin 1) : Fin 52 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 12) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 15) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 15) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 15)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
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

def points : Fin 3 → Fin 15 := ![0, 13, 14]
def point_index : Fin 15 → Fin 3 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

private def law1445 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 1))))⟩
private theorem count1445 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1445} = 628 := by native_decide

private def law3521 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count3521 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law3521} = 552 := by native_decide

end Magma.InvariantNonabelianCppAugmentedAffine13Index3Fixed2Symmetric0

open Magma.InvariantNonabelianCppAugmentedAffine13Index3Fixed2Symmetric0 Magma.InvariantFamily

theorem Equation3521_not_termStructuralFromFin_Equation1445_invariantFamilyCount : ¬ Law3521.TermStructuralFromFin Law1445 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1445) (fun p => OrbitTest points (fam p) law3521)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1445, count3521]
    decide

/-- info: 'Equation3521_not_termStructuralFromFin_Equation1445_invariantFamilyCount' depends on axioms: [propext,
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
 count1445._native.native_decide.ax_1_1,
 count3521._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3521_not_termStructuralFromFin_Equation1445_invariantFamilyCount

