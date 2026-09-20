import equational_theories.Definability.CachedWordImages

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectiveFanoFlags1453And3317

def genData : Array (Array (Fin 21)) := #[#[0, 1, 2, 5, 4, 3, 8, 7, 6, 13, 12, 14, 10, 9, 11, 19, 20, 18, 17, 15, 16], #[0, 1, 2, 6, 7, 8, 3, 4, 5, 11, 10, 9, 12, 14, 13, 18, 20, 19, 15, 17, 16], #[0, 2, 1, 15, 16, 17, 18, 20, 19, 9, 10, 11, 12, 14, 13, 3, 4, 5, 6, 8, 7], #[0, 10, 12, 3, 9, 15, 6, 11, 18, 4, 1, 7, 2, 16, 20, 5, 13, 19, 8, 17, 14], #[1, 0, 2, 9, 10, 11, 13, 12, 14, 3, 4, 5, 7, 6, 8, 15, 16, 17, 19, 18, 20]]
def gen (i : Fin 5) (x : Fin 21) : Fin 21 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 21)) := #[#[0, 1, 2, 5, 4, 3, 8, 7, 6, 13, 12, 14, 10, 9, 11, 19, 20, 18, 17, 15, 16], #[0, 1, 2, 6, 7, 8, 3, 4, 5, 11, 10, 9, 12, 14, 13, 18, 20, 19, 15, 17, 16], #[0, 2, 1, 15, 16, 17, 18, 20, 19, 9, 10, 11, 12, 14, 13, 3, 4, 5, 6, 8, 7], #[0, 10, 12, 3, 9, 15, 6, 11, 18, 4, 1, 7, 2, 16, 20, 5, 13, 19, 8, 17, 14], #[1, 0, 2, 9, 10, 11, 13, 12, 14, 3, 4, 5, 7, 6, 8, 15, 16, 17, 19, 18, 20]]
def genInv (i : Fin 5) (x : Fin 21) : Fin 21 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 21)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 19]]
def probe (i : Fin 1) (x : Fin 21) : Fin 21 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 21)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 19]]
def probeInv (i : Fin 1) (x : Fin 21) : Fin 21 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 21)) := #[#[0, 0, 0, 0, 2, 0, 0, 2, 0, 12, 0, 12, 0, 10, 10, 0, 1, 0, 0, 0, 1], #[1, 1, 1, 7, 1, 7, 4, 1, 4, 1, 2, 1, 2, 1, 1, 1, 0, 1, 1, 1, 0], #[2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 1, 2, 1, 2, 2, 20, 2, 20, 16, 16, 2], #[3, 5, 3, 3, 3, 3, 3, 5, 3, 3, 15, 15, 3, 4, 3, 3, 9, 9, 3, 4, 3], #[7, 4, 7, 4, 4, 4, 1, 4, 1, 5, 4, 4, 4, 3, 4, 5, 4, 4, 4, 3, 4], #[5, 3, 5, 5, 5, 5, 5, 3, 5, 4, 5, 5, 19, 5, 19, 4, 5, 5, 13, 5, 13], #[6, 8, 6, 6, 8, 6, 6, 6, 6, 18, 18, 6, 6, 6, 7, 6, 6, 7, 6, 11, 11], #[4, 7, 4, 1, 7, 1, 7, 7, 7, 7, 7, 8, 7, 7, 6, 7, 7, 6, 8, 7, 7], #[8, 6, 8, 8, 6, 8, 8, 8, 8, 8, 8, 7, 17, 17, 8, 14, 14, 8, 7, 8, 8], #[11, 9, 9, 9, 15, 15, 10, 9, 9, 9, 9, 9, 11, 9, 9, 9, 3, 3, 10, 9, 9], #[10, 12, 12, 11, 10, 10, 9, 10, 10, 10, 10, 10, 10, 0, 0, 11, 10, 10, 9, 10, 10], #[9, 11, 11, 10, 11, 11, 11, 18, 18, 11, 11, 11, 9, 11, 11, 10, 11, 11, 11, 6, 6], #[12, 10, 10, 12, 12, 14, 12, 12, 13, 0, 12, 0, 12, 12, 12, 12, 12, 13, 12, 14, 12], #[14, 13, 13, 19, 19, 13, 13, 13, 12, 13, 14, 13, 13, 13, 13, 13, 13, 12, 5, 13, 5], #[13, 14, 14, 14, 14, 12, 17, 17, 14, 14, 13, 14, 14, 14, 14, 8, 8, 14, 14, 12, 14], #[15, 15, 17, 15, 9, 9, 15, 15, 16, 15, 3, 3, 15, 15, 16, 15, 15, 15, 15, 15, 17], #[20, 20, 16, 17, 16, 16, 16, 16, 15, 17, 16, 16, 16, 16, 15, 16, 16, 16, 2, 2, 16], #[17, 17, 15, 16, 17, 17, 14, 14, 17, 16, 17, 17, 8, 8, 17, 17, 17, 17, 17, 17, 15], #[18, 18, 19, 18, 18, 20, 18, 11, 11, 6, 6, 18, 18, 20, 18, 18, 19, 18, 18, 18, 18], #[19, 19, 18, 13, 13, 19, 20, 19, 19, 19, 19, 20, 5, 19, 5, 19, 18, 19, 19, 19, 19], #[16, 16, 20, 20, 20, 18, 19, 20, 20, 20, 20, 19, 20, 18, 20, 2, 20, 2, 20, 20, 20]]
def sourceRow (i : Fin 21) (x : Fin 21) : Fin 21 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 5) : Equiv.Perm (Fin 21) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 21) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 5)) := #[[], [4], [2, 4], [3, 4], [3, 2, 4], [4, 3, 4], [4, 3, 2, 4], [2, 4, 3, 4], [3, 4, 3, 4], [2, 4, 3, 2, 4], [3, 4, 3, 2, 4], [3, 2, 4, 3, 4], [4, 3, 4, 3, 4], [3, 2, 4, 3, 2, 4], [4, 3, 4, 3, 2, 4], [4, 3, 2, 4, 3, 4], [2, 4, 3, 4, 3, 4], [4, 3, 2, 4, 3, 2, 4], [2, 4, 3, 4, 3, 2, 4], [2, 4, 3, 2, 4, 3, 4], [0, 2, 4, 3, 4, 3, 4], [4, 2, 3, 4, 3, 4, 2, 3, 0, 2, 4, 3, 4, 3, 4], [4, 2, 4, 2, 4], [3, 2], [4, 2], [4, 3], [4, 3, 2], [2, 4, 2], [3, 4, 2], [2, 4, 3], [3, 4, 3], [2, 4, 3, 2], [3, 4, 3, 2], [3, 2, 4, 2], [4, 3, 4, 2], [3, 2, 4, 3], [4, 3, 4, 3], [3, 2, 4, 3, 2], [4, 3, 4, 3, 2], [4, 3, 2, 4, 2], [2, 4, 3, 4, 2], [3, 4, 3, 4, 2], [4, 3, 2, 4, 3], [2, 4, 3, 4, 3], [3, 4, 3, 4, 3], [4, 3, 2, 4, 3, 2], [2, 4, 3, 4, 3, 2], [3, 4, 3, 4, 3, 2], [2, 4, 3, 2, 4, 2], [3, 4, 3, 2, 4, 2], [3, 2, 4, 3, 4, 2], [4, 3, 4, 3, 4, 2], [2, 4, 3, 2, 4, 3], [3, 4, 3, 2, 4, 3], [0, 2, 4, 3, 4, 3], [3, 2, 4, 3, 4, 3], [4, 3, 4, 3, 4, 3], [3, 4, 3, 2, 4, 3, 2], [3, 2, 4, 3, 4, 3, 2], [4, 3, 4, 3, 4, 3, 2], [3, 2, 4, 3, 2, 4, 2], [4, 3, 4, 3, 2, 4, 2], [4, 3, 2, 4, 3, 4, 2], [2, 4, 3, 4, 3, 4, 2], [3, 2, 4, 3, 2, 4, 3], [4, 3, 4, 3, 2, 4, 3], [3, 0, 2, 4, 3, 4, 3], [4, 3, 2, 4, 3, 4, 3], [2, 4, 3, 4, 3, 4, 3], [4, 3, 4, 3, 2, 4, 3, 2], [4, 3, 2, 4, 3, 4, 3, 2], [2, 4, 3, 4, 3, 4, 3, 2], [4, 3, 2, 4, 3, 2, 4, 2], [2, 4, 3, 4, 3, 2, 4, 2], [2, 4, 3, 2, 4, 3, 4, 2], [0, 2, 4, 3, 4, 3, 4, 2], [4, 3, 2, 4, 3, 2, 4, 3], [2, 4, 3, 4, 3, 2, 4, 3], [4, 3, 0, 2, 4, 3, 4, 3], [2, 4, 3, 2, 4, 3, 4, 3], [0, 2, 4, 3, 4, 3, 4, 3], [2, 4, 3, 4, 3, 2, 4, 3, 2], [2, 4, 3, 2, 4, 3, 4, 3, 2], [0, 2, 4, 3, 4, 3, 4, 3, 2], [3, 4, 2, 3, 4, 2, 4, 0, 2, 4, 3, 4, 3], [4, 3, 4, 2, 3, 4, 2, 4, 0, 2, 4, 3, 4, 3, 4], [1, 0], [2, 0], [4, 0], [2, 1], [4, 1], [0, 2], [4, 1, 0], [4, 2, 0], [2, 4, 0], [3, 4, 0], [4, 2, 1], [2, 4, 1], [3, 4, 1], [4, 0, 2], [0, 2, 4], [3, 4, 1, 0], [2, 4, 2, 0], [3, 4, 2, 0], [3, 2, 4, 0], [4, 3, 4, 0], [2, 4, 2, 1], [3, 4, 2, 1], [3, 2, 4, 1], [4, 3, 4, 1], [2, 4, 0, 2], [3, 4, 0, 2], [3, 0, 2, 4], [4, 3, 4, 1, 0], [3, 2, 4, 2, 0], [4, 3, 4, 2, 0], [4, 3, 2, 4, 0], [2, 4, 3, 4, 0], [3, 4, 3, 4, 0], [3, 2, 4, 2, 1], [4, 3, 4, 2, 1], [4, 3, 2, 4, 1], [2, 4, 3, 4, 1], [3, 4, 3, 4, 1], [3, 2, 4, 0, 2], [4, 3, 4, 0, 2], [4, 3, 0, 2, 4], [0, 2, 4, 3, 4], [2, 4, 3, 4, 1, 0], [3, 4, 3, 4, 1, 0], [4, 3, 2, 4, 2, 0], [2, 4, 3, 4, 2, 0], [3, 4, 3, 4, 2, 0], [3, 4, 3, 2, 4, 0], [3, 2, 4, 3, 4, 0], [4, 3, 4, 3, 4, 0], [4, 3, 2, 4, 2, 1], [2, 4, 3, 4, 2, 1], [3, 4, 3, 4, 2, 1], [2, 4, 3, 2, 4, 1], [3, 4, 3, 2, 4, 1], [0, 2, 4, 3, 4, 1], [3, 2, 4, 3, 4, 1], [4, 3, 4, 3, 4, 1], [4, 3, 2, 4, 0, 2], [2, 4, 3, 4, 0, 2], [3, 4, 3, 4, 0, 2], [0, 2, 4, 3, 4, 2], [3, 4, 3, 0, 2, 4], [3, 0, 2, 4, 3, 4], [3, 2, 4, 3, 4, 1, 0], [4, 3, 4, 3, 4, 1, 0], [2, 4, 3, 2, 4, 2, 0], [3, 4, 3, 2, 4, 2, 0], [0, 2, 4, 3, 4, 2, 0], [3, 2, 4, 3, 4, 2, 0], [4, 3, 4, 3, 4, 2, 0], [4, 3, 4, 3, 2, 4, 0], [4, 3, 2, 4, 3, 4, 0], [2, 4, 3, 4, 3, 4, 0], [3, 4, 3, 2, 4, 2, 1], [3, 2, 4, 3, 4, 2, 1], [4, 3, 4, 3, 4, 2, 1], [3, 2, 4, 3, 2, 4, 1], [4, 3, 4, 3, 2, 4, 1], [3, 0, 2, 4, 3, 4, 1], [4, 3, 2, 4, 3, 4, 1], [2, 4, 3, 4, 3, 4, 1], [3, 4, 3, 2, 4, 0, 2], [3, 2, 4, 3, 4, 0, 2], [4, 3, 4, 3, 4, 0, 2], [3, 0, 2, 4, 3, 4, 2], [4, 3, 4, 3, 0, 2, 4], [4, 3, 0, 2, 4, 3, 4], [4, 3, 2, 4, 3, 4, 1, 0], [2, 4, 3, 4, 3, 4, 1, 0], [3, 2, 4, 3, 2, 4, 2, 0], [4, 3, 4, 3, 2, 4, 2, 0], [3, 0, 2, 4, 3, 4, 2, 0], [4, 3, 2, 4, 3, 4, 2, 0], [2, 4, 3, 4, 3, 4, 2, 0], [2, 4, 3, 4, 3, 2, 4, 0], [2, 4, 3, 2, 4, 3, 4, 0], [0, 2, 4, 3, 4, 3, 4, 0], [4, 3, 4, 3, 2, 4, 2, 1], [4, 3, 2, 4, 3, 4, 2, 1], [2, 4, 3, 4, 3, 4, 2, 1], [4, 3, 2, 4, 3, 2, 4, 1], [2, 4, 3, 4, 3, 2, 4, 1], [4, 3, 0, 2, 4, 3, 4, 1], [2, 4, 3, 2, 4, 3, 4, 1], [0, 2, 4, 3, 4, 3, 4, 1], [4, 3, 4, 3, 2, 4, 0, 2], [4, 3, 2, 4, 3, 4, 0, 2], [2, 4, 3, 4, 3, 4, 0, 2], [4, 3, 0, 2, 4, 3, 4, 2], [2, 4, 3, 4, 3, 0, 2, 4], [2, 4, 3, 2, 4, 3, 4, 1, 0], [0, 2, 4, 3, 4, 3, 4, 1, 0], [4, 3, 2, 4, 3, 2, 4, 2, 0], [2, 4, 3, 4, 3, 2, 4, 2, 0], [4, 3, 0, 2, 4, 3, 4, 2, 0], [2, 4, 3, 2, 4, 3, 4, 2, 0], [0, 2, 4, 3, 4, 3, 4, 2, 0], [2, 4, 3, 4, 3, 2, 4, 2, 1], [2, 4, 3, 2, 4, 3, 4, 2, 1], [0, 2, 4, 3, 4, 3, 4, 2, 1], [2, 4, 3, 4, 3, 2, 4, 0, 2], [2, 4, 3, 2, 4, 3, 4, 0, 2], [0, 2, 4, 3, 4, 3, 4, 0, 2], [3, 1], [3, 2, 1], [4, 3, 1], [4, 3, 2, 1], [2, 4, 3, 1], [3, 4, 3, 1], [0, 2, 4, 3], [3, 4, 3, 2, 1], [3, 2, 4, 3, 1], [4, 3, 4, 3, 1], [3, 0, 2, 4, 3], [4, 3, 4, 3, 2, 1], [4, 3, 2, 4, 3, 1], [2, 4, 3, 4, 3, 1], [3, 4, 3, 4, 3, 1], [4, 3, 0, 2, 4, 3], [2, 4, 3, 4, 3, 2, 1], [3, 4, 3, 4, 3, 2, 1], [2, 4, 3, 2, 4, 3, 1], [3, 4, 3, 2, 4, 3, 1], [0, 2, 4, 3, 4, 3, 1], [3, 2, 4, 3, 4, 3, 1], [4, 3, 4, 3, 4, 3, 1], [3, 4, 3, 0, 2, 4, 3], [3, 2, 4, 3, 4, 3, 2, 1], [4, 3, 4, 3, 4, 3, 2, 1], [3, 2, 4, 3, 2, 4, 3, 1], [4, 3, 4, 3, 2, 4, 3, 1], [3, 0, 2, 4, 3, 4, 3, 1], [4, 3, 2, 4, 3, 4, 3, 1], [2, 4, 3, 4, 3, 4, 3, 1], [4, 3, 4, 3, 0, 2, 4, 3], [4, 3, 2, 4, 3, 4, 3, 2, 1], [2, 4, 3, 4, 3, 4, 3, 2, 1], [4, 3, 2, 4, 3, 2, 4, 3, 1], [2, 4, 3, 4, 3, 2, 4, 3, 1], [4, 3, 0, 2, 4, 3, 4, 3, 1], [2, 4, 3, 2, 4, 3, 4, 3, 1], [0, 2, 4, 3, 4, 3, 4, 3, 1], [3, 4, 3, 0, 2, 4, 3, 4, 2], [2, 4, 3, 4, 3, 0, 2, 4, 3], [0, 2, 4, 3, 4, 3, 4, 3, 2, 1]]
def words (i : Fin 252) : List (Fin 5) := wordsData.getD i.val []
def repData : Array (Fin 21 × Fin 21) := #[(0, 0), (0, 1), (0, 3), (0, 4)]
def rep (i : Fin 4) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 4 × Fin 252)) := #[#[(0, 0), (1, 0), (1, 22), (2, 0), (3, 0), (2, 85), (2, 84), (3, 84), (2, 86), (3, 21), (1, 21), (3, 210), (1, 23), (3, 23), (3, 211), (2, 22), (3, 22), (2, 87), (2, 89), (2, 91), (3, 89)], #[(1, 1), (0, 1), (1, 24), (3, 25), (1, 25), (3, 212), (3, 26), (1, 26), (3, 213), (2, 1), (3, 1), (2, 88), (3, 90), (2, 90), (2, 92), (2, 24), (3, 24), (2, 93), (2, 99), (2, 96), (3, 96)], #[(1, 2), (1, 27), (0, 2), (2, 27), (3, 27), (2, 102), (2, 110), (3, 106), (2, 106), (2, 2), (3, 2), (2, 94), (3, 97), (2, 100), (2, 97), (3, 29), (1, 29), (3, 214), (3, 31), (3, 216), (1, 31)], #[(2, 12), (3, 12), (2, 135), (0, 12), (1, 12), (1, 51), (2, 143), (3, 143), (2, 151), (1, 56), (3, 56), (3, 232), (2, 51), (3, 51), (2, 156), (1, 59), (3, 59), (3, 235), (2, 162), (3, 162), (2, 170)], #[(3, 5), (1, 5), (3, 109), (1, 36), (0, 5), (1, 38), (3, 34), (1, 34), (3, 120), (3, 36), (2, 5), (2, 34), (2, 105), (3, 38), (2, 125), (3, 219), (2, 109), (2, 120), (2, 115), (3, 221), (2, 113)], #[(2, 14), (3, 14), (2, 157), (1, 61), (1, 14), (0, 14), (2, 172), (3, 164), (2, 164), (3, 61), (2, 61), (2, 177), (3, 65), (1, 65), (3, 237), (3, 184), (2, 192), (2, 184), (3, 241), (1, 69), (3, 69)], #[(2, 15), (3, 15), (2, 158), (2, 166), (3, 166), (2, 174), (0, 15), (1, 15), (1, 62), (3, 239), (3, 67), (1, 67), (2, 62), (2, 179), (3, 62), (2, 185), (2, 193), (3, 185), (1, 70), (3, 242), (3, 70)], #[(3, 6), (1, 6), (3, 121), (3, 39), (1, 39), (3, 136), (1, 42), (0, 6), (1, 45), (2, 39), (2, 6), (3, 42), (2, 116), (2, 144), (3, 45), (2, 130), (2, 126), (3, 225), (3, 222), (2, 136), (2, 121)], #[(2, 17), (3, 17), (2, 173), (2, 189), (3, 187), (2, 187), (1, 72), (1, 17), (0, 17), (2, 199), (2, 72), (3, 72), (3, 76), (3, 244), (1, 76), (3, 246), (3, 78), (1, 78), (3, 195), (2, 201), (2, 195)], #[(3, 8), (2, 8), (2, 118), (1, 44), (3, 44), (3, 224), (3, 41), (2, 41), (2, 132), (0, 8), (1, 8), (1, 41), (3, 123), (2, 123), (2, 129), (1, 47), (3, 47), (3, 227), (3, 138), (2, 138), (2, 146)], #[(1, 3), (3, 3), (3, 98), (3, 30), (2, 3), (2, 28), (3, 32), (2, 95), (2, 111), (1, 30), (0, 3), (1, 32), (1, 28), (3, 28), (3, 107), (3, 215), (2, 98), (2, 107), (3, 217), (2, 103), (2, 101)], #[(3, 10), (2, 10), (2, 133), (3, 49), (2, 49), (2, 153), (1, 53), (3, 53), (3, 229), (1, 49), (1, 10), (0, 10), (3, 140), (2, 148), (2, 140), (3, 160), (2, 168), (2, 160), (1, 57), (3, 233), (3, 57)], #[(1, 4), (3, 4), (3, 108), (2, 33), (2, 4), (3, 35), (2, 124), (2, 104), (3, 37), (3, 33), (1, 33), (3, 119), (0, 4), (1, 35), (1, 37), (2, 114), (2, 112), (3, 220), (2, 119), (3, 218), (2, 108)], #[(3, 11), (2, 11), (2, 134), (3, 231), (3, 55), (1, 55), (2, 155), (2, 50), (3, 50), (2, 142), (3, 142), (2, 150), (1, 11), (0, 11), (1, 50), (2, 161), (2, 169), (3, 161), (3, 234), (1, 58), (3, 58)], #[(3, 13), (2, 13), (2, 149), (2, 176), (2, 60), (3, 60), (3, 236), (3, 64), (1, 64), (2, 165), (3, 163), (2, 163), (1, 13), (1, 60), (0, 13), (3, 238), (3, 66), (1, 66), (2, 178), (3, 171), (2, 171)], #[(2, 16), (2, 159), (3, 16), (1, 71), (3, 71), (3, 243), (2, 186), (2, 194), (3, 186), (1, 68), (3, 68), (3, 240), (2, 63), (2, 180), (3, 63), (0, 16), (1, 16), (1, 63), (2, 167), (2, 175), (3, 167)], #[(3, 7), (3, 122), (1, 7), (3, 223), (2, 122), (2, 137), (2, 131), (2, 128), (3, 226), (3, 43), (2, 7), (2, 40), (2, 117), (2, 145), (3, 46), (1, 43), (0, 7), (1, 46), (3, 40), (3, 137), (1, 40)], #[(2, 18), (2, 181), (3, 18), (3, 204), (2, 207), (2, 204), (3, 250), (3, 81), (1, 81), (3, 73), (2, 73), (2, 200), (3, 77), (3, 245), (1, 77), (1, 73), (1, 18), (0, 18), (2, 196), (2, 188), (3, 188)], #[(2, 19), (2, 182), (3, 19), (2, 205), (2, 208), (3, 205), (1, 82), (3, 82), (3, 249), (3, 247), (3, 79), (1, 79), (2, 74), (3, 74), (2, 202), (2, 190), (3, 190), (2, 197), (0, 19), (1, 74), (1, 19)], #[(2, 20), (2, 183), (3, 20), (3, 251), (3, 83), (1, 83), (3, 206), (2, 209), (2, 206), (2, 203), (2, 75), (3, 75), (3, 80), (1, 80), (3, 248), (2, 198), (3, 191), (2, 191), (1, 75), (0, 20), (1, 20)], #[(3, 9), (3, 139), (1, 9), (2, 152), (2, 141), (3, 230), (3, 228), (2, 139), (2, 154), (2, 48), (2, 9), (3, 52), (2, 127), (3, 54), (2, 147), (3, 48), (1, 48), (3, 147), (1, 52), (1, 54), (0, 9)]]
def tr (x y : Fin 21) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 4 → ℕ := ![1, 3, 3, 5]
def valuesData : Array (Array (Fin 21)) := #[#[0], #[0, 1, 2], #[0, 3, 6], #[0, 1, 2, 4, 7]]
def values (i : Fin 4) (j : Fin (sizes i)) : Fin 21 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 252)) := #[#[21, 22], #[84, 85], #[21, 0], #[85, 0]]
def stabilizers (i : Fin 4) (j : Fin 2) : Fin 252 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 4) → Fin (sizes i)
def imageData : Array (Array (Fin 21)) :=
  wordImageData genPerm words
def image (i : Fin 252) (x : Fin 21) : Fin 21 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 252) (x : Fin 21) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 21) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 21) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 21)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
  obtain ⟨p, hp⟩ := classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg
  exact ⟨p, (fam_eq_family p).trans hp⟩

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

private abbrev test653 (p : Params) : Prop := ∀ y z : Fin 21, 0 = ((fam p).op 0 ((fam p).op y ((fam p).op ((fam p).op z y) 0)))
private theorem restricted653 : ∀ p : Params, test653 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target653 : ∀ p : Params, @Equation653 (Fin 21) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted653 p (ht 0)

private abbrev test1230 (p : Params) : Prop := ∀ y z : Fin 21, 0 = ((fam p).op 0 ((fam p).op ((fam p).op ((fam p).op 0 y) 0) z))
private theorem restricted1230 : ∀ p : Params, test1230 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target1230 : ∀ p : Params, @Equation1230 (Fin 21) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted1230 p (ht 0)

private abbrev test1633 (p : Params) : Prop := ∀ y z : Fin 21, 0 = ((fam p).op ((fam p).op 0 0) ((fam p).op ((fam p).op 0 y) z))
private theorem restricted1633 : ∀ p : Params, test1633 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target1633 : ∀ p : Params, @Equation1633 (Fin 21) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted1633 p (ht 0)

private abbrev test3264 (p : Params) : Prop := ∀ y z : Fin 21, ((fam p).op 0 0) = ((fam p).op 0 ((fam p).op y ((fam p).op z 0)))
private theorem restricted3264 : ∀ p : Params, test3264 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target3264 : ∀ p : Params, @Equation3264 (Fin 21) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted3264 p (ht 0)

private abbrev test3460 (p : Params) : Prop := ∀ y z : Fin 21, ((fam p).op 0 0) = ((fam p).op 0 ((fam p).op ((fam p).op 0 y) z))
private theorem restricted3460 : ∀ p : Params, test3460 p → ¬ Pattern (fam p) probePerm pattern := by native_decide
theorem target3460 : ∀ p : Params, @Equation3460 (Fin 21) (fam p) → ¬ Pattern (fam p) probePerm pattern := by
  intro p ht
  exact restricted3460 p (ht 0)

end Magma.ProjectiveFanoFlags1453And3317

open Magma.ProjectiveFanoFlags1453And3317

theorem Equation653_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317 : ¬ Law653.StructuralFromFin Law1453 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1453.models_iff (Fin 21) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target653 p ((@Law653.models_iff (Fin 21) (fam p)).mp hp)

/-- info: 'Equation653_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation653_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted653._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation653_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317

theorem Equation1633_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317 : ¬ Law1633.StructuralFromFin Law1453 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1453.models_iff (Fin 21) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1633 p ((@Law1633.models_iff (Fin 21) (fam p)).mp hp)

/-- info: 'Equation1633_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1633_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted1633._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1633_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317

theorem Equation3264_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317 : ¬ Law3264.StructuralFromFin Law1453 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1453.models_iff (Fin 21) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3264 p ((@Law3264.models_iff (Fin 21) (fam p)).mp hp)

/-- info: 'Equation3264_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3264_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted3264._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3264_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317

theorem Equation3460_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317 : ¬ Law3460.StructuralFromFin Law1453 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law1453.models_iff (Fin 21) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3460 p ((@Law3460.models_iff (Fin 21) (fam p)).mp hp)

/-- info: 'Equation3460_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3460_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted3460._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3460_not_structuralFromFin_Equation1453_projectiveFanoFlags1453And3317

theorem Equation1230_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317 : ¬ Law1230.StructuralFromFin Law3317 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3317.models_iff (Fin 21) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target1230 p ((@Law1230.models_iff (Fin 21) (fam p)).mp hp)

/-- info: 'Equation1230_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation1230_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted1230._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1230_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317

theorem Equation3460_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317 : ¬ Law3460.StructuralFromFin Law3317 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law3317.models_iff (Fin 21) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    exact target3460 p ((@Law3460.models_iff (Fin 21) (fam p)).mp hp)

/-- info: 'Equation3460_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3460_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317._native.native_decide.ax_1_1,
 gen_inverse._native.native_decide.ax_1_1,
 probe_inverse._native.native_decide.ax_1_1,
 source_generators._native.native_decide.ax_1_1,
 source_pattern._native.native_decide.ax_1_1,
 stabilizers_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_complete._native.native_decide.ax_1_1,
 restricted3460._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3460_not_structuralFromFin_Equation3317_projectiveFanoFlags1453And3317

