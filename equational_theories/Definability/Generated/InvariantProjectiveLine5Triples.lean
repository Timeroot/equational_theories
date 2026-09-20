import equational_theories.Definability.CachedWordImages
import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantProjectiveLine5Triples

def genData : Array (Array (Fin 20)) := #[#[11, 12, 10, 0, 18, 16, 5, 17, 6, 4, 15, 13, 2, 14, 3, 1, 19, 9, 7, 8], #[4, 5, 6, 0, 7, 8, 1, 9, 2, 3, 16, 17, 10, 18, 11, 12, 19, 13, 14, 15], #[2, 0, 3, 1, 5, 9, 7, 6, 4, 8, 11, 15, 13, 12, 10, 14, 18, 16, 19, 17], #[3, 15, 12, 14, 9, 6, 8, 18, 19, 17, 2, 0, 1, 11, 13, 10, 5, 7, 4, 16], #[3, 6, 8, 9, 0, 1, 2, 4, 5, 7, 12, 14, 15, 17, 18, 19, 10, 11, 13, 16], #[1, 3, 0, 2, 8, 4, 7, 6, 9, 5, 14, 10, 13, 12, 15, 11, 17, 19, 16, 18]]
def gen (i : Fin 6) (x : Fin 20) : Fin 20 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 20)) := #[#[3, 15, 12, 14, 9, 6, 8, 18, 19, 17, 2, 0, 1, 11, 13, 10, 5, 7, 4, 16], #[3, 6, 8, 9, 0, 1, 2, 4, 5, 7, 12, 14, 15, 17, 18, 19, 10, 11, 13, 16], #[1, 3, 0, 2, 8, 4, 7, 6, 9, 5, 14, 10, 13, 12, 15, 11, 17, 19, 16, 18], #[11, 12, 10, 0, 18, 16, 5, 17, 6, 4, 15, 13, 2, 14, 3, 1, 19, 9, 7, 8], #[4, 5, 6, 0, 7, 8, 1, 9, 2, 3, 16, 17, 10, 18, 11, 12, 19, 13, 14, 15], #[2, 0, 3, 1, 5, 9, 7, 6, 4, 8, 11, 15, 13, 12, 10, 14, 18, 16, 19, 17]]
def genInv (i : Fin 6) (x : Fin 20) : Fin 20 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 20)) := #[]
def probe (i : Fin 0) (x : Fin 20) : Fin 20 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 20)) := #[]
def probeInv (i : Fin 0) (x : Fin 20) : Fin 20 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 20)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13], #[14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14], #[15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15], #[16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16], #[17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17], #[18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18], #[19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]]
def sourceRow (i : Fin 20) (x : Fin 20) : Fin 20 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 6) : Equiv.Perm (Fin 20) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 20) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 6)) := #[[], [0], [1], [2], [3], [5], [0, 0], [1, 0], [2, 0], [4, 0], [5, 0], [0, 1], [1, 1], [2, 1], [3, 1], [5, 1], [1, 2], [3, 2], [2, 1, 0], [5, 1, 0], [4, 2, 3, 1, 2], [4], [0, 2], [2, 2], [4, 2], [1, 3], [2, 3], [3, 3], [4, 3], [5, 3], [2, 4], [3, 4], [4, 4], [5, 4], [0, 5], [1, 5], [3, 5], [4, 5], [1, 0, 0], [4, 0, 0], [0, 1, 0], [1, 1, 0], [3, 1, 0], [1, 2, 0], [2, 2, 0], [4, 2, 0], [0, 4, 0], [2, 4, 0], [3, 4, 0], [4, 4, 0], [5, 4, 0], [1, 5, 0], [4, 5, 0], [0, 0, 1], [1, 0, 1], [2, 0, 1], [5, 0, 1], [0, 1, 1], [0, 2, 1], [2, 2, 1], [3, 2, 1], [2, 3, 1], [5, 3, 1], [0, 5, 1], [3, 5, 1], [2, 0, 2], [4, 0, 2], [0, 1, 2], [2, 1, 2], [3, 1, 2], [0, 2, 2], [1, 2, 2], [1, 3, 2], [2, 3, 2], [4, 3, 2], [0, 4, 2], [2, 4, 2], [0, 1, 3], [1, 1, 3], [2, 1, 3], [5, 1, 3], [1, 2, 3], [1, 3, 3], [4, 3, 3], [0, 4, 3], [2, 4, 3], [3, 4, 3], [4, 4, 3], [4, 5, 3], [2, 0, 4], [5, 0, 4], [3, 2, 4], [2, 3, 4], [3, 3, 4], [4, 3, 4], [3, 4, 4], [0, 5, 4], [4, 0, 5], [3, 1, 5], [1, 3, 5], [0, 4, 5], [1, 1, 0, 0], [2, 1, 0, 0], [5, 1, 0, 0], [4, 4, 0, 0], [1, 0, 1, 0], [0, 2, 1, 0], [2, 2, 1, 0], [3, 5, 1, 0], [1, 2, 2, 0], [2, 0, 4, 0], [5, 0, 4, 0], [3, 4, 4, 0], [0, 1, 0, 1], [2, 2, 0, 1], [0, 0, 1, 1], [0, 2, 2, 1], [5, 4, 0, 2], [5, 0, 4, 2], [0, 1, 0, 1, 0]]
def words (i : Fin 120) : List (Fin 6) := wordsData.getD i.val []
def repData : Array (Fin 20 × Fin 20) := #[(0, 0), (0, 1), (0, 3), (0, 7), (0, 8), (0, 19)]
def rep (i : Fin 6) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 6 × Fin 120)) := #[#[(0, 0), (1, 0), (1, 119), (2, 0), (2, 20), (1, 20), (1, 71), (3, 0), (4, 0), (3, 71), (1, 70), (2, 25), (1, 25), (3, 119), (3, 25), (4, 25), (4, 20), (3, 70), (3, 20), (5, 0)], #[(1, 110), (0, 5), (2, 5), (1, 5), (1, 90), (3, 30), (3, 5), (1, 30), (2, 30), (4, 5), (2, 26), (4, 80), (3, 110), (1, 80), (1, 26), (3, 80), (3, 90), (4, 26), (5, 5), (3, 26)], #[(1, 3), (2, 3), (0, 3), (1, 111), (4, 3), (2, 33), (3, 3), (1, 33), (3, 33), (1, 89), (3, 79), (1, 29), (3, 111), (1, 79), (4, 79), (2, 29), (3, 29), (5, 3), (4, 29), (3, 89)], #[(2, 23), (1, 46), (1, 23), (0, 4), (3, 21), (4, 21), (1, 21), (3, 23), (1, 113), (2, 21), (4, 46), (3, 105), (1, 105), (3, 46), (2, 4), (1, 4), (5, 4), (3, 113), (3, 4), (4, 4)], #[(2, 2), (1, 76), (4, 2), (3, 76), (0, 2), (1, 2), (1, 116), (2, 76), (1, 84), (3, 2), (1, 78), (3, 78), (4, 78), (3, 112), (3, 84), (5, 2), (1, 112), (2, 78), (3, 116), (4, 84)], #[(1, 35), (3, 35), (2, 13), (4, 13), (1, 100), (0, 13), (2, 35), (1, 62), (3, 13), (1, 13), (3, 100), (1, 81), (3, 67), (4, 62), (5, 13), (3, 81), (2, 67), (4, 67), (1, 67), (3, 62)], #[(1, 75), (3, 16), (3, 37), (1, 98), (1, 16), (2, 16), (0, 16), (4, 16), (2, 37), (1, 37), (3, 75), (4, 63), (2, 60), (5, 16), (4, 60), (3, 98), (3, 63), (1, 60), (1, 63), (3, 60)], #[(3, 68), (1, 118), (1, 42), (3, 12), (2, 12), (1, 68), (4, 12), (0, 12), (1, 12), (2, 42), (4, 87), (3, 42), (5, 12), (2, 53), (3, 118), (4, 42), (1, 87), (3, 87), (3, 53), (1, 53)], #[(4, 15), (2, 15), (3, 24), (1, 24), (1, 15), (3, 15), (2, 24), (1, 61), (0, 15), (1, 69), (3, 88), (5, 15), (3, 85), (4, 61), (1, 88), (3, 69), (3, 61), (1, 85), (4, 69), (2, 85)], #[(3, 32), (4, 32), (1, 32), (2, 14), (3, 59), (1, 115), (1, 14), (2, 32), (1, 59), (0, 14), (5, 14), (3, 115), (4, 14), (3, 28), (3, 40), (1, 40), (4, 28), (3, 14), (2, 28), (1, 28)], #[(1, 72), (2, 10), (3, 72), (4, 47), (1, 92), (3, 22), (3, 96), (4, 10), (3, 92), (5, 10), (0, 10), (1, 22), (2, 22), (1, 10), (1, 47), (3, 47), (2, 92), (1, 96), (4, 22), (3, 10)], #[(2, 1), (4, 77), (1, 77), (3, 77), (3, 104), (1, 104), (4, 1), (3, 82), (5, 1), (3, 65), (1, 109), (0, 1), (1, 1), (2, 65), (3, 109), (1, 65), (1, 82), (3, 1), (2, 82), (4, 65)], #[(1, 34), (3, 66), (3, 99), (1, 17), (4, 34), (3, 34), (2, 43), (5, 17), (3, 17), (4, 17), (2, 34), (1, 99), (0, 17), (4, 66), (1, 66), (2, 17), (3, 52), (1, 52), (1, 43), (3, 43)], #[(3, 48), (1, 73), (1, 6), (3, 117), (3, 73), (4, 6), (5, 6), (2, 41), (4, 73), (3, 6), (1, 48), (2, 6), (4, 48), (0, 6), (2, 48), (1, 117), (1, 41), (3, 93), (3, 41), (1, 93)], #[(3, 101), (1, 101), (4, 9), (2, 9), (3, 27), (5, 9), (4, 31), (3, 54), (1, 31), (3, 31), (1, 27), (3, 9), (1, 44), (2, 27), (0, 9), (1, 9), (4, 27), (2, 31), (3, 44), (1, 54)], #[(4, 50), (3, 97), (2, 8), (1, 97), (5, 8), (3, 74), (3, 91), (4, 8), (3, 36), (1, 74), (3, 50), (1, 50), (2, 36), (1, 8), (1, 36), (0, 8), (3, 8), (4, 36), (1, 91), (2, 74)], #[(4, 18), (3, 108), (3, 103), (5, 18), (1, 58), (2, 18), (3, 58), (1, 103), (3, 56), (4, 51), (2, 56), (1, 18), (3, 18), (1, 108), (4, 56), (3, 51), (0, 18), (1, 56), (1, 51), (2, 103)], #[(3, 57), (4, 7), (5, 7), (3, 95), (2, 7), (4, 57), (1, 57), (3, 39), (1, 39), (3, 114), (1, 7), (3, 86), (1, 95), (3, 7), (2, 39), (4, 95), (1, 86), (0, 7), (2, 57), (1, 114)], #[(3, 83), (5, 11), (4, 94), (3, 38), (3, 11), (1, 94), (1, 38), (3, 94), (4, 38), (2, 49), (4, 11), (2, 11), (1, 83), (3, 107), (3, 49), (1, 107), (1, 11), (2, 38), (0, 11), (1, 49)], #[(5, 19), (3, 102), (3, 106), (4, 19), (4, 45), (3, 55), (3, 64), (1, 102), (2, 19), (1, 64), (3, 45), (4, 55), (3, 19), (1, 106), (1, 19), (2, 55), (2, 102), (1, 45), (1, 55), (0, 19)]]
def tr (x y : Fin 20) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 6 → ℕ := ![2, 20, 4, 20, 4, 2]
def valuesData : Array (Array (Fin 20)) := #[#[0, 19], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], #[0, 3, 16, 19], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], #[0, 8, 11, 19], #[0, 19]]
def values (i : Fin 6) (j : Fin (sizes i)) : Fin 20 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 120)) := #[#[20], #[0], #[119], #[0], #[71], #[20]]
def stabilizers (i : Fin 6) (j : Fin 1) : Fin 120 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def imageData : Array (Array (Fin 20)) :=
  wordImageData genPerm words
def image (i : Fin 120) (x : Fin 20) : Fin 20 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 120) (x : Fin 20) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 20) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 20) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 20)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
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

def points : Fin 1 → Fin 20 := ![0]
def point_index (x : Fin 20) : Fin 1 := 0

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

private def law1109 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))) (.Leaf 0)))⟩
private theorem count1109 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1109} = 6 := by native_decide

private def law1322 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)) (.Leaf 0)))⟩
private theorem count1322 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1322} = 8 := by native_decide

end Magma.InvariantProjectiveLine5Triples

open Magma.InvariantProjectiveLine5Triples Magma.InvariantFamily

theorem Equation1109_not_termStructuralFromFin_Equation1322_invariantFamilyCount : ¬ Law1109.TermStructuralFromFin Law1322 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1322) (fun p => OrbitTest points (fam p) law1109)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1322, count1109]
    decide

/-- info: 'Equation1109_not_termStructuralFromFin_Equation1322_invariantFamilyCount' depends on axioms: [propext,
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
 count1109._native.native_decide.ax_1_1,
 count1322._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1109_not_termStructuralFromFin_Equation1322_invariantFamilyCount

