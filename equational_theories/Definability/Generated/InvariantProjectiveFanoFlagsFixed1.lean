import equational_theories.Definability.CachedWordImages
import equational_theories.Definability.OrbitInvariantCounting
import Mathlib.Data.ZMod.Basic

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.InvariantProjectiveFanoFlagsFixed1

def genData : Array (Array (Fin 22)) := #[#[0, 2, 1, 15, 16, 17, 18, 20, 19, 9, 10, 11, 12, 14, 13, 3, 4, 5, 6, 8, 7, 21], #[12, 13, 14, 3, 5, 4, 18, 19, 20, 9, 10, 11, 0, 1, 2, 15, 17, 16, 6, 7, 8, 21], #[2, 1, 0, 3, 4, 5, 8, 7, 6, 15, 16, 17, 20, 19, 18, 9, 10, 11, 14, 13, 12, 21], #[6, 7, 8, 3, 4, 5, 0, 1, 2, 9, 11, 10, 18, 19, 20, 15, 17, 16, 12, 13, 14, 21], #[0, 1, 2, 5, 4, 3, 8, 7, 6, 13, 12, 14, 10, 9, 11, 19, 20, 18, 17, 15, 16, 21], #[0, 1, 2, 6, 7, 8, 3, 4, 5, 11, 10, 9, 12, 14, 13, 18, 20, 19, 15, 17, 16, 21]]
def gen (i : Fin 6) (x : Fin 22) : Fin 22 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 22)) := #[#[0, 2, 1, 15, 16, 17, 18, 20, 19, 9, 10, 11, 12, 14, 13, 3, 4, 5, 6, 8, 7, 21], #[12, 13, 14, 3, 5, 4, 18, 19, 20, 9, 10, 11, 0, 1, 2, 15, 17, 16, 6, 7, 8, 21], #[2, 1, 0, 3, 4, 5, 8, 7, 6, 15, 16, 17, 20, 19, 18, 9, 10, 11, 14, 13, 12, 21], #[6, 7, 8, 3, 4, 5, 0, 1, 2, 9, 11, 10, 18, 19, 20, 15, 17, 16, 12, 13, 14, 21], #[0, 1, 2, 5, 4, 3, 8, 7, 6, 13, 12, 14, 10, 9, 11, 19, 20, 18, 17, 15, 16, 21], #[0, 1, 2, 6, 7, 8, 3, 4, 5, 11, 10, 9, 12, 14, 13, 18, 20, 19, 15, 17, 16, 21]]
def genInv (i : Fin 6) (x : Fin 22) : Fin 22 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 22)) := #[]
def probe (i : Fin 0) (x : Fin 22) : Fin 22 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 22)) := #[]
def probeInv (i : Fin 0) (x : Fin 22) : Fin 22 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 22)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], #[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], #[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8], #[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9], #[10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10], #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13], #[14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14], #[15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15], #[16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16], #[17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17], #[18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18], #[19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19], #[20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20], #[21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21]]
def sourceRow (i : Fin 22) (x : Fin 22) : Fin 22 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 6) : Equiv.Perm (Fin 22) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 0) : Equiv.Perm (Fin 22) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 6)) := #[[], [1], [2], [3], [2, 1], [3, 1], [4, 1], [0, 2], [1, 2], [3, 2], [5, 3], [0, 2, 1], [4, 2, 1], [4, 3, 1], [5, 3, 1], [3, 4, 1], [1, 0, 2], [0, 3, 2], [5, 3, 2], [5, 0, 2, 1], [2, 5, 3, 1], [2, 3, 0, 4, 5, 3, 1], [0], [1, 0], [2, 0], [3, 0], [0, 3], [2, 1, 0], [4, 1, 0], [0, 2, 0], [1, 2, 0], [3, 2, 0], [5, 3, 0], [5, 2, 1], [4, 0, 3], [5, 0, 3], [0, 2, 1, 0], [3, 4, 1, 0], [1, 0, 2, 0], [0, 3, 2, 0], [5, 3, 2, 0], [0, 4, 2, 1], [2, 5, 0, 3], [2, 0, 1, 4, 2, 5, 3, 1], [0, 2, 0, 1, 4, 2, 5, 0, 3], [5], [5, 0], [5, 1], [4, 2], [5, 2], [4, 3], [0, 4], [1, 4], [3, 4], [1, 5], [2, 5], [3, 5], [4, 2, 0], [5, 2, 0], [4, 3, 0], [1, 4, 0], [3, 4, 0], [2, 5, 0], [3, 5, 0], [0, 4, 1], [1, 4, 1], [5, 4, 1], [2, 5, 1], [3, 5, 1], [4, 0, 2], [5, 0, 2], [5, 1, 2], [0, 4, 2], [1, 4, 2], [1, 5, 2], [3, 5, 2], [0, 4, 3], [1, 4, 3], [5, 4, 3], [2, 5, 3], [3, 5, 3], [1, 0, 4], [3, 0, 4], [3, 1, 4], [0, 3, 4], [1, 5, 4], [3, 5, 4], [2, 1, 5], [3, 1, 5], [1, 2, 5], [3, 2, 5], [4, 2, 1, 0], [5, 2, 1, 0], [1, 4, 1, 0], [4, 0, 2, 0], [5, 0, 2, 0], [5, 1, 2, 0], [0, 4, 2, 0], [1, 4, 2, 0], [1, 5, 2, 0], [3, 5, 2, 0], [0, 4, 3, 0], [1, 4, 3, 0], [5, 4, 3, 0], [2, 5, 3, 0], [3, 5, 3, 0], [3, 1, 4, 0], [0, 3, 4, 0], [1, 2, 5, 0], [3, 2, 5, 0], [4, 0, 2, 1], [1, 4, 2, 1], [1, 5, 2, 1], [3, 5, 2, 1], [1, 4, 3, 1], [3, 5, 3, 1], [1, 0, 4, 1], [3, 0, 4, 1], [3, 1, 4, 1], [0, 3, 4, 1], [1, 5, 4, 1], [3, 5, 4, 1], [4, 1, 0, 2], [1, 4, 0, 2], [3, 4, 0, 2], [3, 5, 0, 2], [3, 5, 1, 2], [4, 0, 3, 2], [3, 5, 3, 2], [1, 0, 4, 2], [3, 0, 4, 2], [3, 1, 5, 2], [1, 4, 0, 3], [3, 5, 0, 3], [1, 5, 4, 3], [3, 5, 4, 3], [1, 2, 5, 3], [3, 2, 5, 3], [2, 1, 0, 4], [5, 3, 1, 4], [4, 3, 1, 5], [0, 3, 2, 5], [5, 0, 2, 1, 0], [0, 4, 2, 1, 0], [1, 4, 2, 1, 0], [1, 5, 2, 1, 0], [3, 1, 4, 1, 0], [0, 3, 4, 1, 0], [4, 1, 0, 2, 0], [1, 4, 0, 2, 0], [3, 5, 0, 2, 0], [3, 5, 1, 2, 0], [4, 0, 3, 2, 0], [3, 5, 3, 2, 0], [1, 0, 4, 2, 0], [3, 0, 4, 2, 0], [1, 5, 4, 3, 0], [3, 5, 4, 3, 0], [5, 3, 1, 4, 0], [0, 3, 2, 5, 0], [3, 5, 0, 2, 1], [3, 1, 5, 2, 1], [1, 2, 5, 3, 1], [3, 2, 5, 3, 1], [2, 1, 0, 4, 1], [5, 3, 1, 4, 1], [3, 5, 0, 2, 1, 0], [5, 3, 1, 4, 1, 0]]
def words (i : Fin 168) : List (Fin 6) := wordsData.getD i.val []
def repData : Array (Fin 22 × Fin 22) := #[(0, 0), (0, 1), (0, 3), (0, 4), (0, 9), (0, 10), (0, 21), (21, 0), (21, 21)]
def rep (i : Fin 9) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 9 × Fin 168)) := #[#[(0, 0), (1, 0), (1, 22), (2, 0), (3, 0), (2, 44), (2, 45), (3, 45), (2, 43), (4, 0), (5, 0), (4, 45), (5, 44), (4, 44), (4, 51), (2, 22), (3, 22), (2, 51), (2, 46), (2, 21), (3, 21), (6, 0)], #[(1, 29), (0, 7), (1, 7), (4, 7), (5, 7), (4, 69), (4, 70), (5, 70), (4, 72), (2, 29), (3, 29), (2, 95), (3, 94), (2, 94), (2, 97), (2, 7), (3, 7), (2, 72), (2, 70), (2, 69), (3, 69), (6, 7)], #[(1, 24), (1, 2), (0, 2), (2, 2), (3, 2), (2, 48), (2, 49), (3, 49), (2, 55), (2, 24), (3, 24), (2, 58), (3, 57), (2, 57), (2, 62), (4, 2), (5, 2), (4, 55), (4, 49), (4, 48), (5, 48), (6, 2)], #[(2, 80), (3, 80), (2, 137), (0, 10), (1, 10), (1, 32), (2, 10), (3, 10), (2, 79), (5, 10), (4, 80), (4, 10), (2, 105), (3, 104), (2, 104), (5, 79), (4, 136), (4, 79), (2, 32), (3, 32), (2, 136), (6, 10)], #[(4, 160), (5, 134), (4, 134), (1, 41), (0, 19), (1, 19), (4, 19), (5, 19), (4, 41), (3, 142), (2, 166), (2, 142), (2, 160), (3, 143), (2, 143), (3, 41), (2, 156), (2, 41), (2, 19), (3, 19), (2, 134), (6, 19)], #[(2, 128), (3, 128), (2, 135), (1, 40), (1, 18), (0, 18), (2, 18), (3, 18), (2, 78), (3, 40), (2, 153), (2, 40), (4, 128), (5, 78), (4, 78), (3, 103), (2, 157), (2, 103), (4, 18), (5, 18), (4, 135), (6, 18)], #[(2, 56), (3, 56), (2, 86), (2, 3), (3, 3), (2, 53), (0, 3), (1, 3), (1, 25), (4, 3), (4, 56), (5, 3), (2, 63), (2, 61), (3, 61), (2, 25), (2, 82), (3, 25), (5, 53), (4, 53), (4, 82), (6, 3)], #[(4, 125), (5, 125), (4, 130), (4, 11), (5, 11), (4, 110), (1, 36), (0, 11), (1, 11), (2, 36), (2, 150), (3, 36), (2, 125), (2, 124), (3, 124), (2, 11), (2, 130), (3, 11), (3, 110), (2, 110), (2, 155), (6, 11)], #[(2, 75), (3, 75), (2, 90), (2, 9), (3, 9), (2, 50), (1, 31), (1, 9), (0, 9), (2, 31), (2, 100), (3, 31), (4, 75), (4, 50), (5, 50), (4, 9), (4, 90), (5, 9), (3, 59), (2, 59), (2, 109), (6, 9)], #[(3, 163), (2, 167), (2, 163), (5, 122), (4, 165), (4, 122), (3, 20), (2, 165), (2, 20), (0, 20), (1, 42), (1, 20), (3, 42), (2, 148), (2, 42), (5, 20), (4, 162), (4, 20), (3, 122), (2, 122), (2, 162), (6, 20)], #[(5, 65), (4, 65), (4, 116), (3, 6), (2, 65), (2, 6), (3, 66), (2, 93), (2, 66), (1, 6), (0, 6), (1, 28), (5, 6), (4, 6), (4, 64), (3, 64), (2, 116), (2, 64), (3, 28), (2, 28), (2, 120), (6, 6)], #[(3, 121), (2, 146), (2, 121), (3, 15), (2, 118), (2, 15), (5, 118), (4, 118), (4, 119), (1, 15), (1, 37), (0, 15), (3, 37), (2, 37), (2, 147), (3, 117), (2, 117), (2, 119), (5, 15), (4, 15), (4, 117), (6, 15)], #[(5, 52), (4, 52), (4, 81), (2, 1), (2, 52), (3, 1), (2, 47), (2, 60), (3, 47), (4, 1), (5, 1), (4, 47), (0, 1), (1, 1), (1, 23), (2, 23), (2, 81), (3, 23), (2, 54), (3, 54), (2, 85), (6, 1)], #[(3, 149), (2, 149), (2, 154), (4, 16), (4, 123), (5, 16), (2, 71), (2, 123), (3, 71), (2, 38), (3, 38), (2, 96), (1, 38), (0, 16), (1, 16), (2, 16), (2, 129), (3, 16), (4, 71), (5, 71), (4, 129), (6, 16)], #[(3, 98), (2, 98), (2, 108), (2, 8), (2, 73), (3, 8), (4, 74), (4, 73), (5, 73), (2, 30), (3, 30), (2, 99), (1, 30), (1, 8), (0, 8), (4, 8), (4, 89), (5, 8), (2, 74), (3, 74), (2, 89), (6, 8)], #[(2, 115), (2, 158), (3, 115), (5, 127), (4, 139), (4, 127), (2, 14), (2, 139), (3, 14), (5, 14), (4, 115), (4, 14), (2, 133), (2, 152), (3, 133), (0, 14), (1, 35), (1, 14), (2, 35), (2, 127), (3, 35), (6, 14)], #[(4, 161), (4, 114), (5, 114), (3, 12), (2, 114), (2, 12), (2, 33), (2, 132), (3, 33), (3, 92), (2, 164), (2, 92), (2, 161), (2, 91), (3, 91), (1, 12), (0, 12), (1, 33), (4, 33), (4, 12), (5, 12), (6, 12)], #[(2, 113), (2, 144), (3, 113), (3, 13), (2, 111), (2, 13), (4, 112), (4, 111), (5, 111), (3, 140), (2, 140), (2, 145), (4, 113), (4, 13), (5, 13), (1, 13), (1, 34), (0, 13), (2, 112), (2, 34), (3, 34), (6, 13)], #[(2, 68), (2, 106), (3, 68), (2, 5), (2, 83), (3, 5), (5, 83), (4, 83), (4, 84), (4, 5), (4, 68), (5, 5), (2, 88), (3, 88), (2, 107), (2, 26), (3, 26), (2, 84), (0, 5), (1, 5), (1, 26), (6, 5)], #[(2, 126), (2, 141), (3, 126), (4, 17), (4, 141), (5, 17), (3, 101), (2, 159), (2, 101), (2, 39), (2, 151), (3, 39), (4, 126), (5, 76), (4, 76), (2, 17), (3, 17), (2, 76), (1, 39), (0, 17), (1, 17), (6, 17)], #[(4, 131), (4, 77), (5, 77), (2, 4), (2, 77), (3, 4), (3, 67), (2, 102), (2, 67), (2, 27), (2, 138), (3, 27), (2, 131), (3, 87), (2, 87), (4, 4), (5, 4), (4, 67), (1, 27), (1, 4), (0, 4), (6, 4)], #[(7, 0), (7, 7), (7, 2), (7, 10), (7, 19), (7, 18), (7, 3), (7, 11), (7, 9), (7, 20), (7, 6), (7, 15), (7, 1), (7, 16), (7, 8), (7, 14), (7, 12), (7, 13), (7, 5), (7, 17), (7, 4), (8, 0)]]
def tr (x y : Fin 22) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 9 → ℕ := ![2, 4, 22, 6, 6, 4, 2, 2, 1]
def valuesData : Array (Array (Fin 22)) := #[#[0, 21], #[0, 1, 2, 21], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], #[0, 1, 2, 4, 7, 21], #[0, 9, 10, 11, 12, 21], #[0, 10, 12, 21], #[0, 21], #[0, 21], #[21]]
def values (i : Fin 9) (j : Fin (sizes i)) : Fin 22 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 168)) := #[#[21, 0], #[43, 44], #[0, 0], #[44, 0], #[22, 0], #[46, 22], #[21, 0], #[21, 0], #[22, 2]]
def stabilizers (i : Fin 9) (j : Fin 2) : Fin 168 := (stabilizersData.getD i.val #[]).getD j.val 0

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
def imageData : Array (Array (Fin 22)) :=
  wordImageData genPerm words
def image (i : Fin 168) (x : Fin 22) : Fin 22 :=
  (imageData.getD i.val #[]).getD x.val 0
theorem image_correct (i : Fin 168) (x : Fin 22) :
    image i x = wordPerm genPerm (words i) x := by
  exact cachedWord_eq genPerm words i x
@[implicit_reducible] def fam (p : Params) : Magma (Fin 22) :=
  ⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩
theorem fam_eq_family (p : Params) : fam p = family genPerm words tr sizes values p := by
  exact family_eq_of_images genPerm words tr sizes values image image_correct p

@[implicit_reducible] def source : Magma (Fin 22) := ⟨sourceRow⟩
def pattern : Fin 0 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 22)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N := by
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

def points : Fin 2 → Fin 22 := ![0, 21]
def point_index : Fin 22 → Fin 2 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem point_cover : ∀ a,
    wordPerm genPerm (words (tr a a).2) (points (point_index a)) = a := by native_decide

theorem point_moves (p : Params) (a) :
    (fam p).IsEndo (wordPerm genPerm (words (tr a a).2)) :=
  word_endo (fam p) genPerm (family_generators p) _

private def law1032 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 2))) (.Leaf 1)))⟩
private theorem count1032 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1032} = 134 := by native_decide

private def law1033 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 2))) (.Leaf 2)))⟩
private theorem count1033 : Fintype.card {p : Params // Magma.InvariantFamily.OrbitTest points (fam p) law1033} = 140 := by native_decide

end Magma.InvariantProjectiveFanoFlagsFixed1

open Magma.InvariantProjectiveFanoFlagsFixed1 Magma.InvariantFamily

theorem Equation1032_not_termStructuralFromFin_Equation1033_invariantFamilyCount : ¬ Law1032.TermStructuralFromFin Law1033 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (fun i => genPerm i) fam family_injective
    coverage family_generators
    (fun p => OrbitTest points (fam p) law1033) (fun p => OrbitTest points (fam p) law1032)
  · intro p hp φ
    exact (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (orbitTest_iff_satisfies points (fam p) point_index (fun a => wordPerm genPerm (words (tr a a).2)) (point_moves p) point_cover _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1033, count1032]
    decide

/-- info: 'Equation1032_not_termStructuralFromFin_Equation1033_invariantFamilyCount' depends on axioms: [propext,
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
 count1032._native.native_decide.ax_1_1,
 count1033._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1032_not_termStructuralFromFin_Equation1033_invariantFamilyCount

