import equational_theories.Definability.TransitiveInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianSetactionTuples5Choose2Symmetric

def genData : Array (Array (Fin 20)) := #[#[4, 5, 6, 7, 0, 1, 2, 3, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19], #[1, 0, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 14, 13, 15, 16, 18, 17, 19], #[0, 2, 1, 3, 4, 6, 5, 7, 12, 13, 14, 15, 8, 9, 10, 11, 16, 17, 19, 18], #[0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 16, 17, 18, 19, 12, 13, 14, 15]]
def gen (i : Fin 4) (x : Fin 20) : Fin 20 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 20)) := #[#[4, 5, 6, 7, 0, 1, 2, 3, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19], #[1, 0, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 14, 13, 15, 16, 18, 17, 19], #[0, 2, 1, 3, 4, 6, 5, 7, 12, 13, 14, 15, 8, 9, 10, 11, 16, 17, 19, 18], #[0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 16, 17, 18, 19, 12, 13, 14, 15]]
def genInv (i : Fin 4) (x : Fin 20) : Fin 20 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 20)) := #[]
def probe (i : Fin 0) (x : Fin 20) : Fin 20 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 20)) := #[]
def probeInv (i : Fin 0) (x : Fin 20) : Fin 20 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 20)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13], #[14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14], #[15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15], #[16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16], #[17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17], #[18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18], #[19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]]
def sourceRow (i : Fin 20) (x : Fin 20) : Fin 20 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 4) : Equiv.Perm (Fin 20) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 20) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 4)) := #[[], [0], [1], [1, 0], [0, 1], [2, 1], [0, 1, 0], [2, 1, 0], [2, 0, 1], [3, 2, 1], [2, 0, 1, 0], [3, 2, 1, 0], [1, 2, 0, 1], [3, 2, 0, 1], [1, 2, 0, 1, 0], [3, 2, 0, 1, 0], [3, 1, 2, 0, 1], [3, 1, 2, 0, 1, 0], [2, 3, 1, 2, 0, 1], [2, 3, 1, 2, 0, 1, 0], [0, 1, 0, 2, 1, 3, 2, 0, 2, 3, 1, 2, 0, 1, 0], [0, 1, 0, 2, 1, 3, 2, 1, 2, 3, 1, 2, 0, 1, 0], [2, 0], [1, 2], [3, 2], [1, 2, 0], [3, 2, 0], [1, 2, 1], [0, 1, 2], [3, 1, 2], [1, 2, 1, 0], [0, 1, 2, 0], [3, 1, 2, 0], [0, 1, 2, 1], [3, 1, 2, 1], [3, 0, 1, 2], [2, 3, 1, 2], [0, 1, 2, 1, 0], [3, 1, 2, 1, 0], [3, 0, 1, 2, 0], [2, 3, 1, 2, 0], [0, 1, 2, 0, 1], [3, 0, 1, 2, 1], [2, 3, 1, 2, 1], [2, 3, 0, 1, 2], [0, 1, 2, 0, 1, 0], [3, 0, 1, 2, 1, 0], [2, 3, 1, 2, 1, 0], [2, 3, 0, 1, 2, 0], [3, 0, 1, 2, 0, 1], [2, 3, 0, 1, 2, 1], [1, 2, 3, 0, 1, 2], [3, 0, 1, 2, 0, 1, 0], [2, 3, 0, 1, 2, 1, 0], [1, 2, 3, 0, 1, 2, 0], [2, 3, 0, 1, 2, 0, 1], [1, 2, 3, 0, 1, 2, 1], [2, 3, 0, 1, 2, 0, 1, 0], [1, 2, 3, 0, 1, 2, 1, 0], [1, 2, 3, 0, 1, 2, 0, 1], [1, 2, 3, 0, 1, 2, 0, 1, 0], [3, 0], [3, 1], [2, 3], [3, 1, 0], [2, 3, 0], [3, 0, 1], [2, 3, 1], [2, 3, 2], [1, 2, 3], [3, 0, 1, 0], [2, 3, 1, 0], [2, 3, 2, 0], [1, 2, 3, 0], [2, 3, 0, 1], [2, 3, 2, 1], [1, 2, 3, 1], [1, 2, 3, 2], [0, 1, 2, 3], [2, 3, 0, 1, 0], [2, 3, 2, 1, 0], [1, 2, 3, 1, 0], [1, 2, 3, 2, 0], [0, 1, 2, 3, 0], [2, 3, 2, 0, 1], [1, 2, 3, 0, 1], [1, 2, 3, 2, 1], [0, 1, 2, 3, 1], [1, 2, 3, 1, 2], [0, 1, 2, 3, 2], [2, 3, 2, 0, 1, 0], [1, 2, 3, 0, 1, 0], [1, 2, 3, 2, 1, 0], [0, 1, 2, 3, 1, 0], [1, 2, 3, 1, 2, 0], [0, 1, 2, 3, 2, 0], [1, 2, 3, 2, 0, 1], [0, 1, 2, 3, 0, 1], [1, 2, 3, 1, 2, 1], [0, 1, 2, 3, 2, 1], [0, 1, 2, 3, 1, 2], [1, 2, 3, 2, 0, 1, 0], [0, 1, 2, 3, 0, 1, 0], [1, 2, 3, 1, 2, 1, 0], [0, 1, 2, 3, 2, 1, 0], [0, 1, 2, 3, 1, 2, 0], [1, 2, 3, 1, 2, 0, 1], [0, 1, 2, 3, 2, 0, 1], [0, 1, 2, 3, 1, 2, 1], [0, 1, 2, 3, 0, 1, 2], [1, 2, 3, 1, 2, 0, 1, 0], [0, 1, 2, 3, 2, 0, 1, 0], [0, 1, 2, 3, 1, 2, 1, 0], [0, 1, 2, 3, 0, 1, 2, 0], [0, 1, 2, 3, 1, 2, 0, 1], [0, 1, 2, 3, 0, 1, 2, 1], [0, 1, 2, 3, 1, 2, 0, 1, 0], [0, 1, 2, 3, 0, 1, 2, 1, 0], [0, 1, 2, 3, 0, 1, 2, 0, 1], [0, 1, 2, 3, 0, 1, 2, 0, 1, 0]]
def words (i : Fin 120) : List (Fin 4) := wordsData.getD i.val []
def repData : Array (Fin 20 × Fin 20) := #[(0, 0), (0, 1), (0, 4), (0, 5), (0, 8), (0, 9), (0, 10)]
def rep (i : Fin 7) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 7 × Fin 120)) := #[#[(0, 0), (1, 0), (1, 20), (1, 24), (2, 0), (3, 0), (3, 20), (3, 24), (4, 0), (5, 0), (6, 0), (6, 21), (4, 20), (5, 20), (6, 20), (6, 63), (4, 24), (5, 24), (6, 24), (6, 68)], #[(1, 2), (0, 2), (1, 23), (1, 29), (4, 2), (5, 2), (6, 2), (6, 62), (2, 2), (3, 2), (3, 23), (3, 29), (4, 23), (6, 23), (5, 23), (6, 69), (4, 29), (6, 29), (5, 29), (6, 77)], #[(1, 5), (1, 27), (0, 5), (1, 36), (4, 5), (6, 5), (5, 5), (6, 67), (4, 27), (6, 27), (5, 27), (6, 76), (2, 5), (3, 5), (3, 27), (3, 36), (4, 36), (6, 36), (6, 88), (5, 36)], #[(1, 9), (1, 34), (1, 43), (0, 9), (4, 9), (6, 9), (6, 75), (5, 9), (4, 34), (6, 34), (6, 86), (5, 34), (4, 43), (6, 43), (6, 98), (5, 43), (2, 9), (3, 9), (3, 34), (3, 43)], #[(2, 1), (3, 1), (3, 22), (3, 26), (0, 1), (1, 1), (1, 22), (1, 26), (5, 1), (4, 1), (6, 1), (6, 61), (5, 22), (4, 22), (6, 22), (6, 65), (5, 26), (4, 26), (6, 26), (6, 72)], #[(4, 4), (5, 4), (6, 4), (6, 66), (1, 4), (0, 4), (1, 28), (1, 35), (3, 4), (2, 4), (3, 28), (3, 35), (6, 28), (4, 28), (5, 28), (6, 78), (6, 35), (4, 35), (5, 35), (6, 89)], #[(4, 8), (6, 8), (5, 8), (6, 74), (1, 8), (1, 33), (0, 8), (1, 44), (6, 33), (4, 33), (5, 33), (6, 87), (3, 8), (2, 8), (3, 33), (3, 44), (6, 44), (4, 44), (6, 100), (5, 44)], #[(4, 13), (6, 13), (6, 84), (5, 13), (1, 13), (1, 42), (1, 50), (0, 13), (6, 42), (4, 42), (6, 99), (5, 42), (6, 50), (4, 50), (6, 108), (5, 50), (3, 13), (2, 13), (3, 42), (3, 50)], #[(3, 3), (2, 3), (3, 25), (3, 32), (5, 3), (4, 3), (6, 3), (6, 64), (0, 3), (1, 3), (1, 25), (1, 32), (5, 25), (6, 25), (4, 25), (6, 73), (5, 32), (6, 32), (4, 32), (6, 82)], #[(5, 6), (4, 6), (6, 6), (6, 70), (3, 6), (2, 6), (3, 31), (3, 39), (1, 6), (0, 6), (1, 31), (1, 39), (6, 31), (5, 31), (4, 31), (6, 83), (6, 39), (5, 39), (4, 39), (6, 95)], #[(6, 12), (4, 12), (5, 12), (6, 85), (6, 41), (4, 41), (5, 41), (6, 97), (1, 12), (1, 41), (0, 12), (1, 51), (3, 12), (3, 41), (2, 12), (3, 51), (6, 51), (6, 109), (4, 51), (5, 51)], #[(6, 16), (4, 16), (6, 96), (5, 16), (6, 49), (4, 49), (6, 107), (5, 49), (1, 16), (1, 49), (1, 56), (0, 16), (6, 56), (6, 115), (4, 56), (5, 56), (3, 16), (3, 49), (2, 16), (3, 56)], #[(3, 7), (3, 30), (2, 7), (3, 40), (5, 7), (6, 7), (4, 7), (6, 71), (5, 30), (6, 30), (4, 30), (6, 81), (0, 7), (1, 7), (1, 30), (1, 40), (5, 40), (6, 40), (6, 94), (4, 40)], #[(5, 10), (6, 10), (4, 10), (6, 79), (3, 10), (3, 37), (2, 10), (3, 48), (6, 37), (5, 37), (4, 37), (6, 93), (1, 10), (0, 10), (1, 37), (1, 48), (6, 48), (5, 48), (6, 105), (4, 48)], #[(6, 14), (5, 14), (4, 14), (6, 91), (6, 45), (5, 45), (4, 45), (6, 102), (3, 14), (3, 45), (2, 14), (3, 54), (1, 14), (1, 45), (0, 14), (1, 54), (6, 54), (6, 113), (5, 54), (4, 54)], #[(6, 18), (6, 106), (4, 18), (5, 18), (6, 55), (6, 114), (4, 55), (5, 55), (6, 59), (6, 118), (4, 59), (5, 59), (1, 18), (1, 55), (1, 59), (0, 18), (3, 18), (3, 55), (3, 59), (2, 18)], #[(3, 11), (3, 38), (3, 47), (2, 11), (5, 11), (6, 11), (6, 80), (4, 11), (5, 38), (6, 38), (6, 92), (4, 38), (5, 47), (6, 47), (6, 103), (4, 47), (0, 11), (1, 11), (1, 38), (1, 47)], #[(5, 15), (6, 15), (6, 90), (4, 15), (3, 15), (3, 46), (3, 53), (2, 15), (6, 46), (5, 46), (6, 104), (4, 46), (6, 53), (5, 53), (6, 112), (4, 53), (1, 15), (0, 15), (1, 46), (1, 53)], #[(6, 17), (5, 17), (6, 101), (4, 17), (6, 52), (5, 52), (6, 111), (4, 52), (3, 17), (3, 52), (3, 58), (2, 17), (6, 58), (6, 117), (5, 58), (4, 58), (1, 17), (1, 52), (0, 17), (1, 58)], #[(6, 19), (6, 110), (5, 19), (4, 19), (6, 57), (6, 116), (5, 57), (4, 57), (6, 60), (6, 119), (5, 60), (4, 60), (3, 19), (3, 57), (3, 60), (2, 19), (1, 19), (1, 57), (1, 60), (0, 19)]]
def tr (x y : Fin 20) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 7 → ℕ := ![2, 6, 2, 6, 6, 6, 20]
def valuesData : Array (Array (Fin 20)) := #[#[0, 4], #[0, 1, 4, 5, 8, 9], #[0, 4], #[0, 1, 4, 5, 8, 9], #[0, 1, 4, 5, 8, 9], #[0, 1, 4, 5, 8, 9], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
def values (i : Fin 7) (j : Fin (sizes i)) : Fin 20 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 120)) := #[#[20, 21], #[21, 0], #[20, 21], #[21, 0], #[21, 0], #[21, 0], #[0, 0]]
def stabilizers (i : Fin 7) (j : Fin 2) : Fin 120 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 20) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 20) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 20)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
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

private def law1632 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 1)))⟩
private theorem count1632 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 20) (fam p) law1632} = 1770 := by native_decide

private def law3459 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 1)))⟩
private theorem count3459 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 20) (fam p) law3459} = 1620 := by native_decide

end Magma.InvariantNonabelianSetactionTuples5Choose2Symmetric

open Magma.InvariantNonabelianSetactionTuples5Choose2Symmetric Magma.InvariantFamily

theorem Equation3459_not_termStructuralFromFin_Equation1632_invariantFamilyCount : ¬ Law3459.TermStructuralFromFin Law1632 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 20) (fam p) law1632) (fun p => PointTest (0 : Fin 20) (fam p) law3459)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1632, count3459]
    decide

/-- info: 'Equation3459_not_termStructuralFromFin_Equation1632_invariantFamilyCount' depends on axioms: [propext,
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
 count1632._native.native_decide.ax_1_1,
 count3459._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3459_not_termStructuralFromFin_Equation1632_invariantFamilyCount

