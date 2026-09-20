import equational_theories.Definability.TransitiveInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantNonabelianSemidirect7By3Q2A1B7

def genData : Array (Array (Fin 21)) := #[#[1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 7, 15, 16, 17, 18, 19, 20, 14], #[7, 9, 11, 13, 8, 10, 12, 14, 16, 18, 20, 15, 17, 19, 0, 2, 4, 6, 1, 3, 5], #[0, 2, 4, 6, 1, 3, 5, 7, 9, 11, 13, 8, 10, 12, 14, 16, 18, 20, 15, 17, 19], #[0, 3, 6, 2, 5, 1, 4, 7, 10, 13, 9, 12, 8, 11, 14, 17, 20, 16, 19, 15, 18], #[6, 0, 1, 2, 3, 4, 5, 13, 7, 8, 9, 10, 11, 12, 20, 14, 15, 16, 17, 18, 19], #[14, 18, 15, 19, 16, 20, 17, 0, 4, 1, 5, 2, 6, 3, 7, 11, 8, 12, 9, 13, 10], #[0, 4, 1, 5, 2, 6, 3, 7, 11, 8, 12, 9, 13, 10, 14, 18, 15, 19, 16, 20, 17], #[0, 5, 3, 1, 6, 4, 2, 7, 12, 10, 8, 13, 11, 9, 14, 19, 17, 15, 20, 18, 16]]
def gen (i : Fin 8) (x : Fin 21) : Fin 21 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 21)) := #[#[6, 0, 1, 2, 3, 4, 5, 13, 7, 8, 9, 10, 11, 12, 20, 14, 15, 16, 17, 18, 19], #[14, 18, 15, 19, 16, 20, 17, 0, 4, 1, 5, 2, 6, 3, 7, 11, 8, 12, 9, 13, 10], #[0, 4, 1, 5, 2, 6, 3, 7, 11, 8, 12, 9, 13, 10, 14, 18, 15, 19, 16, 20, 17], #[0, 5, 3, 1, 6, 4, 2, 7, 12, 10, 8, 13, 11, 9, 14, 19, 17, 15, 20, 18, 16], #[1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 7, 15, 16, 17, 18, 19, 20, 14], #[7, 9, 11, 13, 8, 10, 12, 14, 16, 18, 20, 15, 17, 19, 0, 2, 4, 6, 1, 3, 5], #[0, 2, 4, 6, 1, 3, 5, 7, 9, 11, 13, 8, 10, 12, 14, 16, 18, 20, 15, 17, 19], #[0, 3, 6, 2, 5, 1, 4, 7, 10, 13, 9, 12, 8, 11, 14, 17, 20, 16, 19, 15, 18]]
def genInv (i : Fin 8) (x : Fin 21) : Fin 21 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 21)) := #[]
def probe (i : Fin 0) (x : Fin 21) : Fin 21 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 21)) := #[]
def probeInv (i : Fin 0) (x : Fin 21) : Fin 21 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 21)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13], #[14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14], #[15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15], #[16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16], #[17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17], #[18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18], #[19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19], #[20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]]
def sourceRow (i : Fin 21) (x : Fin 21) : Fin 21 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 8) : Equiv.Perm (Fin 21) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 21) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 8)) := #[[], [0], [1], [4], [5], [0, 0], [1, 0], [3, 0], [5, 0], [6, 0], [7, 0], [0, 1], [4, 1], [1, 4], [5, 4], [0, 5], [4, 5], [1, 0, 0], [0, 1, 0], [5, 3, 0], [6, 5, 0], [1, 4, 6, 6, 5, 0], [3], [6], [7], [2, 0], [2, 1], [3, 1], [6, 1], [7, 1], [0, 2], [3, 2], [4, 2], [5, 2], [0, 3], [4, 3], [5, 3], [2, 4], [3, 4], [4, 4], [6, 4], [7, 4], [6, 5], [7, 5], [0, 6], [4, 6], [0, 7], [4, 7], [0, 0, 0], [2, 0, 0], [7, 0, 0], [2, 1, 0], [3, 1, 0], [6, 1, 0], [7, 1, 0], [0, 2, 0], [3, 2, 0], [5, 2, 0], [4, 3, 0], [0, 5, 0], [7, 5, 0], [0, 6, 0], [4, 7, 0], [1, 0, 1], [2, 0, 1], [3, 0, 1], [5, 0, 1], [6, 0, 1], [7, 0, 1], [0, 2, 1], [3, 2, 1], [4, 2, 1], [0, 3, 1], [2, 4, 1], [3, 4, 1], [6, 4, 1], [7, 4, 1], [4, 6, 1], [0, 7, 1], [4, 7, 1], [2, 0, 2], [3, 0, 2], [5, 0, 2], [7, 0, 2], [0, 3, 2], [5, 3, 2], [3, 4, 2], [5, 4, 2], [4, 5, 2], [1, 0, 3], [2, 0, 3], [5, 0, 3], [1, 4, 3], [2, 4, 3], [5, 4, 3], [0, 5, 3], [4, 5, 3], [2, 1, 4], [7, 1, 4], [5, 3, 4], [6, 5, 4], [7, 5, 4], [2, 0, 5], [6, 0, 5], [7, 0, 5], [2, 4, 5], [6, 4, 5], [7, 4, 5], [0, 6, 5], [4, 6, 5], [1, 0, 6], [1, 4, 6], [5, 0, 7], [5, 4, 7], [3, 2, 1, 0], [5, 3, 2, 0], [3, 2, 0, 1], [3, 0, 2, 1], [0, 3, 2, 1], [3, 4, 2, 1], [2, 0, 3, 1], [5, 3, 0, 2], [5, 0, 3, 2], [0, 5, 3, 2], [4, 5, 3, 2], [5, 3, 4, 2]]
def words (i : Fin 126) : List (Fin 8) := wordsData.getD i.val []
def repData : Array (Fin 21 × Fin 21) := #[(0, 0), (0, 1), (0, 7), (0, 8), (0, 14), (0, 15)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 126)) := #[#[(0, 0), (1, 0), (1, 21), (1, 22), (1, 23), (1, 24), (1, 31), (2, 0), (3, 0), (3, 21), (3, 22), (3, 23), (3, 24), (3, 31), (4, 0), (5, 0), (5, 21), (5, 22), (5, 23), (5, 24), (5, 31)], #[(1, 84), (0, 1), (1, 1), (1, 30), (1, 34), (1, 44), (1, 46), (3, 84), (2, 1), (3, 1), (3, 30), (3, 34), (3, 44), (3, 46), (5, 84), (4, 1), (5, 1), (5, 30), (5, 34), (5, 44), (5, 46)], #[(1, 41), (1, 90), (0, 5), (1, 5), (1, 25), (1, 58), (1, 80), (3, 41), (3, 90), (2, 5), (3, 5), (3, 25), (3, 58), (3, 80), (5, 41), (5, 90), (4, 5), (5, 5), (5, 25), (5, 58), (5, 80)], #[(1, 40), (1, 50), (1, 81), (0, 7), (1, 48), (1, 55), (1, 7), (3, 40), (3, 50), (3, 81), (2, 7), (3, 48), (3, 55), (3, 7), (5, 40), (5, 50), (5, 81), (4, 7), (5, 48), (5, 55), (5, 7)], #[(1, 38), (1, 9), (1, 62), (1, 86), (0, 9), (1, 66), (1, 49), (3, 38), (3, 9), (3, 62), (3, 86), (2, 9), (3, 66), (3, 49), (5, 38), (5, 9), (5, 62), (5, 86), (4, 9), (5, 66), (5, 49)], #[(1, 37), (1, 83), (1, 61), (1, 10), (1, 93), (0, 10), (1, 39), (3, 37), (3, 83), (3, 61), (3, 10), (3, 93), (2, 10), (3, 39), (5, 37), (5, 83), (5, 61), (5, 10), (5, 93), (4, 10), (5, 39)], #[(1, 3), (1, 32), (1, 35), (1, 45), (1, 47), (1, 56), (0, 3), (3, 3), (3, 32), (3, 35), (3, 45), (3, 47), (3, 56), (2, 3), (5, 3), (5, 32), (5, 35), (5, 45), (5, 47), (5, 56), (4, 3)], #[(4, 2), (5, 28), (5, 2), (5, 29), (5, 26), (5, 70), (5, 27), (0, 2), (1, 28), (1, 2), (1, 29), (1, 26), (1, 70), (1, 27), (2, 2), (3, 28), (3, 2), (3, 29), (3, 26), (3, 70), (3, 27)], #[(5, 72), (4, 11), (5, 53), (5, 11), (5, 78), (5, 69), (5, 118), (1, 72), (0, 11), (1, 53), (1, 11), (1, 78), (1, 69), (1, 118), (3, 72), (2, 11), (3, 53), (3, 11), (3, 78), (3, 69), (3, 118)], #[(5, 120), (5, 89), (4, 6), (5, 110), (5, 6), (5, 76), (5, 64), (1, 120), (1, 89), (0, 6), (1, 110), (1, 6), (1, 76), (1, 64), (3, 120), (3, 89), (2, 6), (3, 110), (3, 6), (3, 76), (3, 64)], #[(5, 97), (5, 117), (5, 65), (4, 18), (5, 75), (5, 18), (5, 54), (1, 97), (1, 117), (1, 65), (0, 18), (1, 75), (1, 18), (1, 54), (3, 97), (3, 117), (3, 65), (2, 18), (3, 75), (3, 18), (3, 54)], #[(5, 98), (5, 51), (5, 119), (5, 74), (4, 17), (5, 67), (5, 17), (1, 98), (1, 51), (1, 119), (1, 74), (0, 17), (1, 67), (1, 17), (3, 98), (3, 51), (3, 119), (3, 74), (2, 17), (3, 67), (3, 17)], #[(5, 13), (5, 68), (5, 73), (5, 114), (5, 92), (4, 13), (5, 111), (1, 13), (1, 68), (1, 73), (1, 114), (1, 92), (0, 13), (1, 111), (3, 13), (3, 68), (3, 73), (3, 114), (3, 92), (2, 13), (3, 111)], #[(5, 77), (5, 12), (5, 79), (5, 71), (5, 116), (5, 52), (4, 12), (1, 77), (1, 12), (1, 79), (1, 71), (1, 116), (1, 52), (0, 12), (3, 77), (3, 12), (3, 79), (3, 71), (3, 116), (3, 52), (2, 12)], #[(2, 4), (3, 33), (3, 42), (3, 85), (3, 4), (3, 36), (3, 43), (4, 4), (5, 33), (5, 42), (5, 85), (5, 4), (5, 36), (5, 43), (0, 4), (1, 33), (1, 42), (1, 85), (1, 4), (1, 36), (1, 43)], #[(3, 101), (2, 15), (3, 57), (3, 108), (3, 123), (3, 15), (3, 95), (5, 101), (4, 15), (5, 57), (5, 108), (5, 123), (5, 15), (5, 95), (1, 101), (0, 15), (1, 57), (1, 108), (1, 123), (1, 15), (1, 95)], #[(3, 99), (3, 107), (2, 20), (3, 102), (3, 20), (3, 125), (3, 63), (5, 99), (5, 107), (4, 20), (5, 102), (5, 20), (5, 125), (5, 63), (1, 99), (1, 107), (0, 20), (1, 102), (1, 20), (1, 125), (1, 63)], #[(3, 14), (3, 94), (3, 113), (2, 14), (3, 87), (3, 106), (3, 115), (5, 14), (5, 94), (5, 113), (4, 14), (5, 87), (5, 106), (5, 115), (1, 14), (1, 94), (1, 113), (0, 14), (1, 87), (1, 106), (1, 115)], #[(3, 122), (3, 8), (3, 91), (3, 112), (2, 8), (3, 82), (3, 103), (5, 122), (5, 8), (5, 91), (5, 112), (4, 8), (5, 82), (5, 103), (1, 122), (1, 8), (1, 91), (1, 112), (0, 8), (1, 82), (1, 103)], #[(3, 100), (3, 121), (3, 59), (3, 19), (3, 104), (2, 19), (3, 105), (5, 100), (5, 121), (5, 59), (5, 19), (5, 104), (4, 19), (5, 105), (1, 100), (1, 121), (1, 59), (1, 19), (1, 104), (0, 19), (1, 105)], #[(3, 88), (3, 109), (3, 124), (3, 16), (3, 96), (3, 60), (2, 16), (5, 88), (5, 109), (5, 124), (5, 16), (5, 96), (5, 60), (4, 16), (1, 88), (1, 109), (1, 124), (1, 16), (1, 96), (1, 60), (0, 16)]]
def tr (x y : Fin 21) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![3, 21, 3, 21, 3, 21]
def valuesData : Array (Array (Fin 21)) := #[#[0, 7, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], #[0, 7, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], #[0, 7, 14], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 21 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 126)) := #[#[21], #[0], #[21], #[0], #[21], #[0]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 126 := (stabilizersData.getD i.val #[]).getD j.val 0

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
@[implicit_reducible] def fam (p : Params) : Magma (Fin 21) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 21) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 21)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
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

private def law58 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count58 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law58} = 178 := by native_decide

private def law418 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 2)))))⟩
private theorem count418 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law418} = 621 := by native_decide

private def law1021 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))) (.Leaf 1)))⟩
private theorem count1021 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law1021} = 619 := by native_decide

private def law1437 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count1437 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law1437} = 178 := by native_decide

private def law1525 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count1525 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law1525} = 264 := by native_decide

private def law1701 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Fork (.Fork (.Leaf 2) (.Leaf 0)) (.Leaf 0)))⟩
private theorem count1701 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law1701} = 619 := by native_decide

private def law3264 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count3264 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law3264} = 134 := by native_decide

private def law3526 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 2)) (.Leaf 2)))⟩
private theorem count3526 : Fintype.card {p : Params // Magma.InvariantFamily.PointTest (0 : Fin 21) (fam p) law3526} = 192 := by native_decide

end Magma.InvariantNonabelianSemidirect7By3Q2A1B7

open Magma.InvariantNonabelianSemidirect7By3Q2A1B7 Magma.InvariantFamily

theorem Equation3264_not_termStructuralFromFin_Equation58_invariantFamilyCount : ¬ Law3264.TermStructuralFromFin Law58 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 21) (fam p) law58) (fun p => PointTest (0 : Fin 21) (fam p) law3264)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count58, count3264]
    decide

/-- info: 'Equation3264_not_termStructuralFromFin_Equation58_invariantFamilyCount' depends on axioms: [propext,
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
 count3264._native.native_decide.ax_1_1,
 count58._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3264_not_termStructuralFromFin_Equation58_invariantFamilyCount

theorem Equation1021_not_termStructuralFromFin_Equation418_invariantFamilyCount : ¬ Law1021.TermStructuralFromFin Law418 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 21) (fam p) law418) (fun p => PointTest (0 : Fin 21) (fam p) law1021)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count418, count1021]
    decide

/-- info: 'Equation1021_not_termStructuralFromFin_Equation418_invariantFamilyCount' depends on axioms: [propext,
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
 count1021._native.native_decide.ax_1_1,
 count418._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1021_not_termStructuralFromFin_Equation418_invariantFamilyCount

theorem Equation1701_not_termStructuralFromFin_Equation418_invariantFamilyCount : ¬ Law1701.TermStructuralFromFin Law418 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 21) (fam p) law418) (fun p => PointTest (0 : Fin 21) (fam p) law1701)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count418, count1701]
    decide

/-- info: 'Equation1701_not_termStructuralFromFin_Equation418_invariantFamilyCount' depends on axioms: [propext,
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
 count1701._native.native_decide.ax_1_1,
 count418._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1701_not_termStructuralFromFin_Equation418_invariantFamilyCount

theorem Equation3264_not_termStructuralFromFin_Equation1437_invariantFamilyCount : ¬ Law3264.TermStructuralFromFin Law1437 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 21) (fam p) law1437) (fun p => PointTest (0 : Fin 21) (fam p) law3264)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1437, count3264]
    decide

/-- info: 'Equation3264_not_termStructuralFromFin_Equation1437_invariantFamilyCount' depends on axioms: [propext,
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
 count1437._native.native_decide.ax_1_1,
 count3264._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3264_not_termStructuralFromFin_Equation1437_invariantFamilyCount

theorem Equation3526_not_termStructuralFromFin_Equation1525_invariantFamilyCount : ¬ Law3526.TermStructuralFromFin Law1525 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => PointTest (0 : Fin 21) (fam p) law1525) (fun p => PointTest (0 : Fin 21) (fam p) law3526)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (fam p) (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_transitive _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1525, count3526]
    decide

/-- info: 'Equation3526_not_termStructuralFromFin_Equation1525_invariantFamilyCount' depends on axioms: [propext,
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
 count3526._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3526_not_termStructuralFromFin_Equation1525_invariantFamilyCount

