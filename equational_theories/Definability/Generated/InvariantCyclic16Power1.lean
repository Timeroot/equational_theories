import equational_theories.Definability.InvariantFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantCyclic16Power1

def genData : Array (Array (Fin 16)) := #[#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0], #[0, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13], #[0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11], #[15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 11, 6, 1, 12, 7, 2, 13, 8, 3, 14, 9, 4, 15, 10, 5], #[0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3]]
def gen (i : Fin 6) (x : Fin 16) : Fin 16 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 16)) := #[#[15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 11, 6, 1, 12, 7, 2, 13, 8, 3, 14, 9, 4, 15, 10, 5], #[0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0], #[0, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13], #[0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11]]
def genInv (i : Fin 6) (x : Fin 16) : Fin 16 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 16)) := #[]
def probe (i : Fin 0) (x : Fin 16) : Fin 16 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 16)) := #[]
def probeInv (i : Fin 0) (x : Fin 16) : Fin 16 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 16)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13], #[14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14], #[15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15]]
def sourceRow (i : Fin 16) (x : Fin 16) : Fin 16 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 6) : Equiv.Perm (Fin 16) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 16) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 6)) := #[[], [0], [3], [0, 0], [1, 0], [2, 0], [4, 0], [5, 0], [3, 3], [1, 0, 0], [2, 0, 0], [0, 1, 0], [1, 1, 0], [5, 1, 0], [0, 4, 0], [3, 1, 1, 0], [3, 2, 0, 0, 4, 0], [1], [2], [4], [5], [0, 1], [1, 1], [2, 1], [3, 1], [0, 2], [3, 2], [1, 3], [2, 3], [4, 3], [5, 3], [0, 4], [3, 4], [0, 5], [3, 5], [0, 0, 0], [4, 0, 0], [5, 0, 0], [2, 1, 0], [3, 1, 0], [0, 2, 0], [3, 2, 0], [3, 4, 0], [0, 5, 0], [3, 5, 0], [1, 0, 1], [2, 0, 1], [4, 0, 1], [5, 0, 1], [0, 1, 1], [3, 1, 1], [0, 2, 1], [1, 3, 1], [2, 3, 1], [3, 3, 1], [4, 3, 1], [5, 3, 1], [0, 5, 1], [3, 5, 1], [0, 0, 2], [1, 0, 2], [2, 0, 2], [4, 0, 2], [5, 0, 2], [1, 3, 2], [2, 3, 2], [3, 3, 2], [4, 3, 2], [1, 1, 3], [3, 1, 3], [5, 1, 3], [0, 2, 3], [1, 3, 3], [5, 3, 3], [3, 4, 3], [0, 5, 3], [3, 5, 3], [0, 0, 4], [3, 3, 4], [0, 0, 0, 0], [1, 0, 0, 0], [5, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [2, 1, 0, 0], [3, 1, 0, 0], [5, 1, 0, 0], [3, 2, 0, 0], [0, 4, 0, 0], [0, 5, 0, 0], [3, 5, 0, 0], [1, 0, 1, 0], [2, 0, 1, 0], [4, 0, 1, 0], [5, 0, 1, 0], [0, 1, 1, 0], [1, 3, 1, 0], [2, 3, 1, 0], [4, 3, 1, 0], [5, 3, 1, 0], [0, 5, 1, 0], [3, 5, 1, 0], [0, 0, 2, 0], [1, 0, 2, 0], [2, 0, 2, 0], [4, 0, 2, 0], [1, 3, 2, 0], [2, 3, 2, 0], [3, 3, 2, 0], [4, 3, 2, 0], [0, 0, 4, 0], [3, 3, 4, 0], [0, 2, 0, 1], [3, 4, 0, 1], [1, 0, 1, 1], [2, 0, 1, 1], [4, 0, 1, 1], [5, 0, 1, 1], [3, 1, 0, 0, 0], [0, 5, 0, 0, 0], [2, 3, 1, 0, 0], [4, 3, 1, 0, 0], [3, 3, 2, 0, 0], [0, 0, 4, 0, 0], [0, 0, 2, 0, 1], [3, 3, 4, 0, 1], [2, 3, 1, 0, 0, 0], [4, 3, 1, 0, 0, 0]]
def words (i : Fin 128) : List (Fin 6) := wordsData.getD i.val []
def repData : Array (Fin 16 × Fin 16) := #[(0, 0), (0, 1), (0, 2), (0, 4), (0, 8)]
def rep (i : Fin 5) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 5 × Fin 128)) := #[#[(0, 0), (1, 0), (2, 0), (1, 17), (3, 0), (1, 18), (2, 17), (1, 16), (4, 0), (1, 22), (2, 18), (1, 19), (3, 17), (1, 20), (2, 23), (1, 23)], #[(1, 51), (0, 1), (1, 1), (2, 1), (1, 21), (3, 1), (1, 25), (2, 21), (1, 57), (4, 1), (1, 49), (2, 25), (1, 31), (3, 21), (1, 33), (2, 51)], #[(2, 103), (1, 103), (0, 3), (1, 3), (2, 3), (1, 39), (3, 3), (1, 59), (2, 39), (1, 105), (4, 3), (1, 83), (2, 59), (1, 77), (3, 39), (1, 76)], #[(1, 30), (2, 56), (1, 60), (0, 4), (1, 35), (2, 35), (1, 4), (3, 30), (1, 108), (2, 4), (1, 56), (4, 4), (1, 45), (2, 30), (1, 114), (3, 4)], #[(3, 11), (1, 75), (2, 92), (1, 92), (0, 11), (1, 79), (2, 79), (1, 11), (3, 41), (1, 41), (2, 11), (1, 94), (4, 11), (1, 107), (2, 41), (1, 74)], #[(1, 29), (3, 29), (1, 115), (2, 46), (1, 46), (0, 5), (1, 55), (2, 55), (1, 85), (3, 5), (1, 5), (2, 29), (1, 67), (4, 5), (1, 61), (2, 5)], #[(2, 40), (1, 36), (3, 9), (1, 73), (2, 101), (1, 112), (0, 9), (1, 98), (2, 96), (1, 9), (3, 40), (1, 40), (2, 9), (1, 101), (4, 9), (1, 96)], #[(1, 68), (2, 81), (1, 88), (3, 13), (1, 81), (2, 13), (1, 124), (0, 13), (1, 121), (2, 68), (1, 82), (3, 68), (1, 102), (2, 82), (1, 13), (4, 13)], #[(4, 15), (1, 15), (2, 119), (1, 123), (3, 100), (1, 119), (2, 100), (1, 126), (0, 15), (1, 127), (2, 15), (1, 118), (3, 15), (1, 122), (2, 118), (1, 100)], #[(1, 70), (4, 12), (1, 12), (2, 87), (1, 111), (3, 70), (1, 90), (2, 70), (1, 120), (0, 12), (1, 125), (2, 12), (1, 80), (3, 12), (1, 87), (2, 80)], #[(2, 42), (1, 99), (4, 10), (1, 95), (2, 10), (1, 42), (3, 42), (1, 37), (2, 97), (1, 97), (0, 10), (1, 113), (2, 95), (1, 72), (3, 10), (1, 10)], #[(1, 28), (2, 6), (1, 62), (4, 6), (1, 65), (2, 28), (1, 6), (3, 6), (1, 89), (2, 53), (1, 53), (0, 6), (1, 47), (2, 47), (1, 116), (3, 28)], #[(3, 44), (1, 71), (2, 14), (1, 109), (4, 14), (1, 91), (2, 44), (1, 14), (3, 14), (1, 44), (2, 106), (1, 106), (0, 14), (1, 93), (2, 91), (1, 69)], #[(1, 27), (3, 7), (1, 117), (2, 27), (1, 48), (4, 7), (1, 52), (2, 7), (1, 110), (3, 27), (1, 7), (2, 48), (1, 64), (0, 7), (1, 63), (2, 52)], #[(2, 8), (1, 54), (3, 8), (1, 66), (2, 54), (1, 86), (4, 8), (1, 104), (2, 43), (1, 78), (3, 54), (1, 43), (2, 84), (1, 84), (0, 8), (1, 8)], #[(1, 2), (2, 2), (1, 24), (3, 2), (1, 26), (2, 24), (1, 58), (4, 2), (1, 50), (2, 26), (1, 32), (3, 24), (1, 34), (2, 38), (1, 38), (0, 2)]]
def tr (x y : Fin 16) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 5 → ℕ := ![2, 16, 8, 4, 2]
def valuesData : Array (Array (Fin 16)) := #[#[0, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 2, 4, 6, 8, 10, 12, 14], #[0, 4, 8, 12], #[0, 8]]
def values (i : Fin 5) (j : Fin (sizes i)) : Fin 16 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 128)) := #[#[16], #[0], #[22], #[18], #[16]]
def stabilizers (i : Fin 5) (j : Fin 1) : Fin 128 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 16) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 16) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 16)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

local instance : AddCommGroup (Fin 16) := inferInstanceAs (AddCommGroup (ZMod 16))

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

theorem translation_words : ∀ a x,
    wordPerm genPerm (List.replicate a.val 0) x = a+x := by native_decide

theorem translations (p : Params) (a) : (fam p).IsEndo (fun x => a+x) := by
  have h := word_endo (fam p) genPerm (family_generators p) (List.replicate a.val 0)
  have he : (wordPerm genPerm (List.replicate a.val 0) : _ → _) = (fun x => a+x) :=
    funext (translation_words a)
  rw [he] at h
  exact h

private def law1027 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0))) (.Leaf 2)))⟩
private theorem count1027 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law1027} = 24 := by native_decide

private def law1235 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 2)) (.Leaf 1)))⟩
private theorem count1235 : Fintype.card {p : Params // Magma.InvariantFamily.ZeroTest (fam p) law1235} = 28 := by native_decide

end Magma.InvariantCyclic16Power1

open Magma.InvariantCyclic16Power1 Magma.InvariantFamily

theorem Equation1027_not_termStructuralFromFin_Equation1235_invariantFamilyCount : ¬ Law1027.TermStructuralFromFin Law1235 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => ZeroTest (fam p) law1235) (fun p => ZeroTest (fam p) law1027)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (fam p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (fam p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1235, count1027]
    decide

/-- info: 'Equation1027_not_termStructuralFromFin_Equation1235_invariantFamilyCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 coherent_values._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 same_orbit._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 tr_rep._native.native_decide.ax_1_1,
 translation_words._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 values_injective._native.native_decide.ax_1_1,
 words_zero._native.native_decide.ax_1_1,
 count1027._native.native_decide.ax_1_1,
 count1235._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1027_not_termStructuralFromFin_Equation1235_invariantFamilyCount

