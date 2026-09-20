import equational_theories.Definability.FiniteSymmetry

/-! Finite orbit-chart certificate; reproduced from the accompanying JSON data. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.Field25Index3Source4

def genData : Array (Array (Fin 25)) := #[#[0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18], #[0, 5, 10, 15, 20, 3, 8, 13, 18, 23, 1, 6, 11, 16, 21, 4, 9, 14, 19, 24, 2, 7, 12, 17, 22], #[0, 6, 12, 18, 24, 8, 14, 15, 21, 2, 11, 17, 23, 4, 5, 19, 20, 1, 7, 13, 22, 3, 9, 10, 16], #[1, 0, 4, 3, 2, 21, 20, 24, 23, 22, 16, 15, 19, 18, 17, 11, 10, 14, 13, 12, 6, 5, 9, 8, 7], #[0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12], #[0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17, 3, 13, 23, 8, 18, 4, 14, 24, 9, 19], #[0, 17, 9, 21, 13, 14, 1, 18, 5, 22, 23, 10, 2, 19, 6, 7, 24, 11, 3, 15, 16, 8, 20, 12, 4]]
def gen (i : Fin 7) (x : Fin 25) : Fin 25 := (genData.getD i.val #[]).getD x.val 0

def genInvData : Array (Array (Fin 25)) := #[#[0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12], #[0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17, 3, 13, 23, 8, 18, 4, 14, 24, 9, 19], #[0, 17, 9, 21, 13, 14, 1, 18, 5, 22, 23, 10, 2, 19, 6, 7, 24, 11, 3, 15, 16, 8, 20, 12, 4], #[1, 0, 4, 3, 2, 21, 20, 24, 23, 22, 16, 15, 19, 18, 17, 11, 10, 14, 13, 12, 6, 5, 9, 8, 7], #[0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18], #[0, 5, 10, 15, 20, 3, 8, 13, 18, 23, 1, 6, 11, 16, 21, 4, 9, 14, 19, 24, 2, 7, 12, 17, 22], #[0, 6, 12, 18, 24, 8, 14, 15, 21, 2, 11, 17, 23, 4, 5, 19, 20, 1, 7, 13, 22, 3, 9, 10, 16]]
def genInv (i : Fin 7) (x : Fin 25) : Fin 25 := (genInvData.getD i.val #[]).getD x.val 0

def probeData : Array (Array (Fin 25)) := #[#[0, 1, 2, 3, 4, 20, 21, 22, 23, 24, 15, 16, 17, 18, 19, 10, 11, 12, 13, 14, 5, 6, 7, 8, 9]]
def probe (i : Fin 1) (x : Fin 25) : Fin 25 := (probeData.getD i.val #[]).getD x.val 0

def probeInvData : Array (Array (Fin 25)) := #[#[0, 1, 2, 3, 4, 20, 21, 22, 23, 24, 15, 16, 17, 18, 19, 10, 11, 12, 13, 14, 5, 6, 7, 8, 9]]
def probeInv (i : Fin 1) (x : Fin 25) : Fin 25 := (probeInvData.getD i.val #[]).getD x.val 0

def sourceRowData : Array (Array (Fin 25)) := #[#[0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17, 3, 13, 23, 8, 18, 4, 14, 24, 9, 19], #[16, 1, 11, 21, 6, 17, 2, 12, 22, 7, 18, 3, 13, 23, 8, 19, 4, 14, 24, 9, 15, 0, 10, 20, 5], #[7, 17, 2, 12, 22, 8, 18, 3, 13, 23, 9, 19, 4, 14, 24, 5, 15, 0, 10, 20, 6, 16, 1, 11, 21], #[23, 8, 18, 3, 13, 24, 9, 19, 4, 14, 20, 5, 15, 0, 10, 21, 6, 16, 1, 11, 22, 7, 17, 2, 12], #[14, 24, 9, 19, 4, 10, 20, 5, 15, 0, 11, 21, 6, 16, 1, 12, 22, 7, 17, 2, 13, 23, 8, 18, 3], #[9, 19, 4, 14, 24, 5, 15, 0, 10, 20, 6, 16, 1, 11, 21, 7, 17, 2, 12, 22, 8, 18, 3, 13, 23], #[20, 5, 15, 0, 10, 21, 6, 16, 1, 11, 22, 7, 17, 2, 12, 23, 8, 18, 3, 13, 24, 9, 19, 4, 14], #[11, 21, 6, 16, 1, 12, 22, 7, 17, 2, 13, 23, 8, 18, 3, 14, 24, 9, 19, 4, 10, 20, 5, 15, 0], #[2, 12, 22, 7, 17, 3, 13, 23, 8, 18, 4, 14, 24, 9, 19, 0, 10, 20, 5, 15, 1, 11, 21, 6, 16], #[18, 3, 13, 23, 8, 19, 4, 14, 24, 9, 15, 0, 10, 20, 5, 16, 1, 11, 21, 6, 17, 2, 12, 22, 7], #[13, 23, 8, 18, 3, 14, 24, 9, 19, 4, 10, 20, 5, 15, 0, 11, 21, 6, 16, 1, 12, 22, 7, 17, 2], #[4, 14, 24, 9, 19, 0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17, 3, 13, 23, 8, 18], #[15, 0, 10, 20, 5, 16, 1, 11, 21, 6, 17, 2, 12, 22, 7, 18, 3, 13, 23, 8, 19, 4, 14, 24, 9], #[6, 16, 1, 11, 21, 7, 17, 2, 12, 22, 8, 18, 3, 13, 23, 9, 19, 4, 14, 24, 5, 15, 0, 10, 20], #[22, 7, 17, 2, 12, 23, 8, 18, 3, 13, 24, 9, 19, 4, 14, 20, 5, 15, 0, 10, 21, 6, 16, 1, 11], #[17, 2, 12, 22, 7, 18, 3, 13, 23, 8, 19, 4, 14, 24, 9, 15, 0, 10, 20, 5, 16, 1, 11, 21, 6], #[8, 18, 3, 13, 23, 9, 19, 4, 14, 24, 5, 15, 0, 10, 20, 6, 16, 1, 11, 21, 7, 17, 2, 12, 22], #[24, 9, 19, 4, 14, 20, 5, 15, 0, 10, 21, 6, 16, 1, 11, 22, 7, 17, 2, 12, 23, 8, 18, 3, 13], #[10, 20, 5, 15, 0, 11, 21, 6, 16, 1, 12, 22, 7, 17, 2, 13, 23, 8, 18, 3, 14, 24, 9, 19, 4], #[1, 11, 21, 6, 16, 2, 12, 22, 7, 17, 3, 13, 23, 8, 18, 4, 14, 24, 9, 19, 0, 10, 20, 5, 15], #[21, 6, 16, 1, 11, 22, 7, 17, 2, 12, 23, 8, 18, 3, 13, 24, 9, 19, 4, 14, 20, 5, 15, 0, 10], #[12, 22, 7, 17, 2, 13, 23, 8, 18, 3, 14, 24, 9, 19, 4, 10, 20, 5, 15, 0, 11, 21, 6, 16, 1], #[3, 13, 23, 8, 18, 4, 14, 24, 9, 19, 0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17], #[19, 4, 14, 24, 9, 15, 0, 10, 20, 5, 16, 1, 11, 21, 6, 17, 2, 12, 22, 7, 18, 3, 13, 23, 8], #[5, 15, 0, 10, 20, 6, 16, 1, 11, 21, 7, 17, 2, 12, 22, 8, 18, 3, 13, 23, 9, 19, 4, 14, 24]]
def sourceRow (i : Fin 25) (x : Fin 25) : Fin 25 := (sourceRowData.getD i.val #[]).getD x.val 0

theorem gen_inverse : ∀ i x, genInv i (gen i x) = x ∧ gen i (genInv i x) = x := by native_decide
def genPerm (i : Fin 7) : Equiv.Perm (Fin 25) := Magma.permOf (gen i) (genInv i) (gen_inverse i)

theorem probe_inverse : ∀ i x, probeInv i (probe i x) = x ∧ probe i (probeInv i x) = x := by native_decide
def probePerm (i : Fin 1) : Equiv.Perm (Fin 25) := Magma.permOf (probe i) (probeInv i) (probe_inverse i)

def wordsData : Array (List (Fin 7)) := #[[], [3], [0, 3], [1, 3], [2, 3], [4, 3], [5, 3], [6, 3], [0, 0, 3], [2, 0, 3], [5, 0, 3], [6, 0, 3], [2, 1, 3], [3, 1, 3], [4, 1, 3], [6, 1, 3], [4, 2, 3], [5, 2, 3], [3, 5, 3], [6, 5, 3], [2, 0, 0, 3], [6, 0, 0, 3], [3, 2, 0, 3], [5, 2, 0, 3], [1, 3, 1, 3], [3, 0, 3, 4, 3], [0], [1], [2], [4], [5], [6], [2, 0], [3, 0], [5, 0], [6, 0], [2, 1], [3, 1], [4, 1], [6, 1], [3, 2], [4, 2], [5, 2], [3, 4], [6, 4], [3, 5], [6, 5], [3, 6], [2, 0, 0], [3, 0, 0], [6, 0, 0], [3, 2, 0], [5, 2, 0], [0, 3, 0], [1, 3, 0], [2, 3, 0], [4, 3, 0], [5, 3, 0], [6, 3, 0], [3, 5, 0], [6, 5, 0], [3, 6, 0], [3, 2, 1], [4, 2, 1], [0, 3, 1], [1, 3, 1], [2, 3, 1], [4, 3, 1], [5, 3, 1], [6, 3, 1], [3, 4, 1], [6, 4, 1], [3, 6, 1], [0, 3, 2], [1, 3, 2], [2, 3, 2], [4, 3, 2], [5, 3, 2], [6, 3, 2], [3, 4, 2], [3, 5, 2], [3, 0, 3], [3, 2, 3], [3, 4, 3], [6, 4, 3], [3, 6, 3], [0, 3, 4], [1, 3, 4], [2, 3, 4], [4, 3, 4], [5, 3, 4], [6, 3, 4], [3, 6, 4], [0, 3, 5], [1, 3, 5], [2, 3, 5], [4, 3, 5], [5, 3, 5], [6, 3, 5], [3, 6, 5], [0, 3, 6], [1, 3, 6], [2, 3, 6], [4, 3, 6], [5, 3, 6], [6, 3, 6], [3, 2, 0, 0], [0, 3, 0, 0], [1, 3, 0, 0], [2, 3, 0, 0], [5, 3, 0, 0], [6, 3, 0, 0], [3, 6, 0, 0], [0, 3, 2, 0], [1, 3, 2, 0], [2, 3, 2, 0], [4, 3, 2, 0], [5, 3, 2, 0], [6, 3, 2, 0], [3, 5, 2, 0], [2, 0, 3, 0], [3, 0, 3, 0], [5, 0, 3, 0], [6, 0, 3, 0], [2, 1, 3, 0], [3, 1, 3, 0], [4, 1, 3, 0], [6, 1, 3, 0], [3, 2, 3, 0], [4, 2, 3, 0], [5, 2, 3, 0], [6, 4, 3, 0], [3, 5, 3, 0], [6, 5, 3, 0], [3, 6, 3, 0], [0, 3, 5, 0], [1, 3, 5, 0], [2, 3, 5, 0], [4, 3, 5, 0], [5, 3, 5, 0], [6, 3, 5, 0], [3, 6, 5, 0], [0, 3, 6, 0], [1, 3, 6, 0], [2, 3, 6, 0], [4, 3, 6, 0], [5, 3, 6, 0], [6, 3, 6, 0], [0, 3, 2, 1], [1, 3, 2, 1], [2, 3, 2, 1], [4, 3, 2, 1], [5, 3, 2, 1], [6, 3, 2, 1], [3, 4, 2, 1], [0, 0, 3, 1], [2, 0, 3, 1], [3, 0, 3, 1], [5, 0, 3, 1], [6, 0, 3, 1], [2, 1, 3, 1], [3, 1, 3, 1], [4, 1, 3, 1], [3, 2, 3, 1], [4, 2, 3, 1], [5, 2, 3, 1], [6, 4, 3, 1], [3, 5, 3, 1], [6, 5, 3, 1], [3, 6, 3, 1], [0, 3, 4, 1], [1, 3, 4, 1], [2, 3, 4, 1], [4, 3, 4, 1], [5, 3, 4, 1], [6, 3, 4, 1], [3, 6, 4, 1], [0, 3, 6, 1], [1, 3, 6, 1], [2, 3, 6, 1], [4, 3, 6, 1], [5, 3, 6, 1], [6, 3, 6, 1], [0, 0, 3, 2], [2, 0, 3, 2], [3, 0, 3, 2], [6, 0, 3, 2], [2, 1, 3, 2], [3, 1, 3, 2], [4, 1, 3, 2], [6, 1, 3, 2], [3, 2, 3, 2], [4, 2, 3, 2], [5, 2, 3, 2], [3, 4, 3, 2], [6, 4, 3, 2], [3, 5, 3, 2], [6, 5, 3, 2], [3, 6, 3, 2], [0, 3, 4, 2], [1, 3, 4, 2], [2, 3, 4, 2], [4, 3, 4, 2], [5, 3, 4, 2], [6, 3, 4, 2], [0, 3, 5, 2], [1, 3, 5, 2], [2, 3, 5, 2], [4, 3, 5, 2], [5, 3, 5, 2], [6, 3, 5, 2], [2, 3, 0, 3], [6, 3, 0, 3], [6, 5, 0, 3], [3, 6, 0, 3], [3, 2, 1, 3], [4, 2, 1, 3], [0, 3, 1, 3], [2, 3, 1, 3], [4, 3, 1, 3], [6, 3, 1, 3], [3, 4, 1, 3], [6, 4, 1, 3], [0, 3, 2, 3], [2, 3, 2, 3], [5, 3, 2, 3], [3, 4, 2, 3], [1, 3, 4, 3], [2, 3, 4, 3], [6, 3, 4, 3], [3, 6, 4, 3], [0, 3, 5, 3], [1, 3, 5, 3], [2, 3, 5, 3], [4, 3, 5, 3], [5, 3, 5, 3], [6, 3, 5, 3], [3, 6, 5, 3], [0, 3, 6, 3], [1, 3, 6, 3], [4, 3, 6, 3], [0, 0, 3, 4], [2, 0, 3, 4], [5, 0, 3, 4], [6, 0, 3, 4], [2, 1, 3, 4], [3, 1, 3, 4], [4, 1, 3, 4], [6, 1, 3, 4], [3, 2, 3, 4], [4, 2, 3, 4], [5, 2, 3, 4], [6, 4, 3, 4], [3, 5, 3, 4], [6, 5, 3, 4], [3, 6, 3, 4], [0, 3, 6, 4], [1, 3, 6, 4], [2, 3, 6, 4], [4, 3, 6, 4], [5, 3, 6, 4], [6, 3, 6, 4], [2, 0, 3, 5], [3, 0, 3, 5], [5, 0, 3, 5], [6, 0, 3, 5], [2, 1, 3, 5], [3, 1, 3, 5], [4, 1, 3, 5], [6, 1, 3, 5], [4, 2, 3, 5], [5, 2, 3, 5], [6, 4, 3, 5], [3, 5, 3, 5], [6, 5, 3, 5], [0, 3, 6, 5], [1, 3, 6, 5], [2, 3, 6, 5], [4, 3, 6, 5], [5, 3, 6, 5], [6, 3, 6, 5], [0, 0, 3, 6], [2, 0, 3, 6], [3, 0, 3, 6], [6, 0, 3, 6], [2, 1, 3, 6], [4, 1, 3, 6], [6, 1, 3, 6], [4, 2, 3, 6], [3, 4, 3, 6], [6, 4, 3, 6], [3, 5, 3, 6], [6, 5, 3, 6], [3, 6, 3, 6], [0, 3, 2, 0, 0], [1, 3, 2, 0, 0], [2, 3, 2, 0, 0], [5, 3, 2, 0, 0], [6, 3, 2, 0, 0], [2, 0, 3, 0, 0], [5, 0, 3, 0, 0], [6, 0, 3, 0, 0], [2, 1, 3, 0, 0], [3, 1, 3, 0, 0], [3, 2, 3, 0, 0], [5, 2, 3, 0, 0], [3, 5, 3, 0, 0], [6, 5, 3, 0, 0], [0, 3, 6, 0, 0], [1, 3, 6, 0, 0], [2, 3, 6, 0, 0], [5, 3, 6, 0, 0], [6, 3, 6, 0, 0], [2, 0, 3, 2, 0], [3, 0, 3, 2, 0], [2, 1, 3, 2, 0], [3, 1, 3, 2, 0], [4, 1, 3, 2, 0], [6, 1, 3, 2, 0], [3, 2, 3, 2, 0], [4, 2, 3, 2, 0], [5, 2, 3, 2, 0], [6, 4, 3, 2, 0], [3, 5, 3, 2, 0], [3, 6, 3, 2, 0], [0, 3, 5, 2, 0], [1, 3, 5, 2, 0], [2, 3, 5, 2, 0], [4, 3, 5, 2, 0], [5, 3, 5, 2, 0], [6, 3, 5, 2, 0], [3, 2, 0, 3, 0], [5, 2, 0, 3, 0], [2, 3, 0, 3, 0], [6, 3, 0, 3, 0], [3, 6, 0, 3, 0], [3, 2, 1, 3, 0], [4, 2, 1, 3, 0], [1, 3, 1, 3, 0], [4, 3, 1, 3, 0], [3, 4, 1, 3, 0], [6, 4, 1, 3, 0], [0, 3, 2, 3, 0], [2, 3, 2, 3, 0], [5, 3, 2, 3, 0], [3, 4, 2, 3, 0], [3, 6, 4, 3, 0], [0, 3, 5, 3, 0], [1, 3, 5, 3, 0], [2, 3, 5, 3, 0], [4, 3, 5, 3, 0], [5, 3, 5, 3, 0], [6, 3, 5, 3, 0], [3, 6, 5, 3, 0], [4, 3, 6, 3, 0], [2, 0, 3, 5, 0], [3, 0, 3, 5, 0], [5, 0, 3, 5, 0], [6, 0, 3, 5, 0], [2, 1, 3, 5, 0], [4, 1, 3, 5, 0], [4, 2, 3, 5, 0], [5, 2, 3, 5, 0], [6, 4, 3, 5, 0], [3, 5, 3, 5, 0], [6, 5, 3, 5, 0], [0, 3, 6, 5, 0], [2, 3, 6, 5, 0], [4, 3, 6, 5, 0], [5, 3, 6, 5, 0], [6, 3, 6, 5, 0], [2, 0, 3, 6, 0], [3, 0, 3, 6, 0], [6, 0, 3, 6, 0], [2, 1, 3, 6, 0], [4, 1, 3, 6, 0], [6, 1, 3, 6, 0], [4, 2, 3, 6, 0], [6, 4, 3, 6, 0], [3, 5, 3, 6, 0], [6, 5, 3, 6, 0], [3, 6, 3, 6, 0], [0, 0, 3, 2, 1], [2, 0, 3, 2, 1], [6, 0, 3, 2, 1], [3, 1, 3, 2, 1], [4, 1, 3, 2, 1], [3, 2, 3, 2, 1], [4, 2, 3, 2, 1], [5, 2, 3, 2, 1], [3, 5, 3, 2, 1], [6, 5, 3, 2, 1], [3, 6, 3, 2, 1], [0, 3, 4, 2, 1], [1, 3, 4, 2, 1], [2, 3, 4, 2, 1], [5, 3, 4, 2, 1], [2, 0, 0, 3, 1], [6, 0, 0, 3, 1], [5, 2, 0, 3, 1], [2, 3, 0, 3, 1], [6, 3, 0, 3, 1], [6, 5, 0, 3, 1], [4, 2, 1, 3, 1], [6, 3, 1, 3, 1], [3, 4, 1, 3, 1], [2, 3, 2, 3, 1], [3, 4, 2, 3, 1], [0, 3, 5, 3, 1], [1, 3, 5, 3, 1], [4, 3, 5, 3, 1], [5, 3, 5, 3, 1], [6, 3, 5, 3, 1], [3, 6, 5, 3, 1], [4, 3, 6, 3, 1], [2, 0, 3, 4, 1], [5, 0, 3, 4, 1], [6, 0, 3, 4, 1], [2, 1, 3, 4, 1], [4, 1, 3, 4, 1], [3, 2, 3, 4, 1], [4, 2, 3, 4, 1], [5, 2, 3, 4, 1], [3, 5, 3, 4, 1], [0, 3, 6, 4, 1], [2, 3, 6, 4, 1], [4, 3, 6, 4, 1], [5, 3, 6, 4, 1], [6, 3, 6, 4, 1], [0, 0, 3, 6, 1], [2, 0, 3, 6, 1], [3, 0, 3, 6, 1], [6, 0, 3, 6, 1], [2, 1, 3, 6, 1], [4, 1, 3, 6, 1], [4, 2, 3, 6, 1], [6, 4, 3, 6, 1], [3, 5, 3, 6, 1], [6, 5, 3, 6, 1], [3, 6, 3, 6, 1], [2, 0, 0, 3, 2], [6, 0, 0, 3, 2], [3, 2, 0, 3, 2], [3, 6, 0, 3, 2], [4, 2, 1, 3, 2], [1, 3, 1, 3, 2], [6, 3, 1, 3, 2], [6, 4, 1, 3, 2], [2, 3, 2, 3, 2], [3, 4, 2, 3, 2], [1, 3, 4, 3, 2], [2, 3, 4, 3, 2], [0, 3, 5, 3, 2], [1, 3, 5, 3, 2], [2, 3, 5, 3, 2], [5, 3, 5, 3, 2], [6, 3, 5, 3, 2], [3, 6, 5, 3, 2], [0, 3, 6, 3, 2], [0, 0, 3, 4, 2], [2, 0, 3, 4, 2], [6, 0, 3, 4, 2], [4, 1, 3, 4, 2], [6, 1, 3, 4, 2], [3, 2, 3, 4, 2], [4, 2, 3, 4, 2], [5, 2, 3, 4, 2], [3, 5, 3, 4, 2], [6, 5, 3, 4, 2], [3, 6, 3, 4, 2], [2, 0, 3, 5, 2], [3, 1, 3, 5, 2], [6, 1, 3, 5, 2], [4, 2, 3, 5, 2], [5, 2, 3, 5, 2], [3, 5, 3, 5, 2], [3, 2, 0, 0, 3], [3, 6, 0, 0, 3], [4, 3, 2, 0, 3], [3, 5, 2, 0, 3], [3, 6, 3, 0, 3], [0, 3, 6, 0, 3], [1, 3, 6, 0, 3], [4, 3, 6, 0, 3], [4, 3, 2, 1, 3], [6, 3, 2, 1, 3], [0, 0, 3, 1, 3], [6, 0, 3, 1, 3], [2, 1, 3, 1, 3], [3, 1, 3, 1, 3], [4, 2, 3, 1, 3], [6, 4, 3, 1, 3], [3, 6, 4, 1, 3], [1, 3, 4, 2, 3], [2, 3, 4, 2, 3], [4, 3, 4, 2, 3], [5, 3, 4, 2, 3], [6, 3, 4, 2, 3], [2, 1, 3, 4, 3], [3, 1, 3, 4, 3], [2, 3, 6, 4, 3], [4, 3, 6, 4, 3], [6, 3, 6, 4, 3], [3, 0, 3, 5, 3], [3, 1, 3, 5, 3], [6, 1, 3, 5, 3], [3, 5, 3, 5, 3], [6, 5, 3, 5, 3], [4, 3, 6, 5, 3], [0, 0, 3, 6, 3], [3, 4, 3, 6, 3], [2, 0, 0, 3, 4], [6, 0, 0, 3, 4], [5, 2, 0, 3, 4], [6, 5, 0, 3, 4], [4, 2, 1, 3, 4], [1, 3, 1, 3, 4], [4, 3, 1, 3, 4], [6, 3, 1, 3, 4], [3, 4, 1, 3, 4], [6, 4, 1, 3, 4], [2, 3, 2, 3, 4], [3, 4, 2, 3, 4], [4, 3, 6, 3, 4], [0, 0, 3, 6, 4], [2, 0, 3, 6, 4], [6, 0, 3, 6, 4], [4, 1, 3, 6, 4], [6, 1, 3, 6, 4], [4, 2, 3, 6, 4], [6, 5, 3, 6, 4], [2, 3, 0, 3, 5], [6, 3, 0, 3, 5], [3, 6, 0, 3, 5], [1, 3, 1, 3, 5], [4, 3, 1, 3, 5], [3, 4, 1, 3, 5], [6, 4, 1, 3, 5], [3, 4, 2, 3, 5], [1, 3, 5, 3, 5], [4, 3, 5, 3, 5], [3, 0, 3, 6, 5], [2, 1, 3, 6, 5], [4, 1, 3, 6, 5], [4, 2, 3, 6, 5], [6, 4, 3, 6, 5], [3, 5, 3, 6, 5], [2, 0, 0, 3, 6], [6, 0, 0, 3, 6], [3, 2, 0, 3, 6], [6, 3, 0, 3, 6], [3, 6, 0, 3, 6], [4, 2, 1, 3, 6], [6, 4, 1, 3, 6], [1, 3, 4, 3, 6], [0, 3, 6, 3, 6], [3, 2, 3, 2, 0, 0], [3, 2, 0, 3, 0, 0], [2, 0, 3, 6, 0, 0], [6, 5, 3, 6, 0, 0], [3, 2, 0, 3, 2, 0], [1, 3, 1, 3, 2, 0], [2, 3, 2, 3, 2, 0], [0, 3, 5, 3, 2, 0], [1, 3, 5, 3, 2, 0], [2, 3, 5, 3, 2, 0], [6, 3, 5, 3, 2, 0], [2, 0, 3, 5, 2, 0], [5, 2, 3, 5, 2, 0], [3, 5, 3, 5, 2, 0], [4, 3, 2, 0, 3, 0], [0, 3, 6, 0, 3, 0], [6, 3, 2, 1, 3, 0], [3, 1, 3, 1, 3, 0], [5, 3, 4, 2, 3, 0], [6, 3, 4, 2, 3, 0], [2, 3, 6, 4, 3, 0], [4, 3, 6, 4, 3, 0], [3, 1, 3, 5, 3, 0], [3, 4, 3, 6, 3, 0], [2, 3, 0, 3, 5, 0], [3, 4, 1, 3, 5, 0], [4, 2, 3, 6, 5, 0], [3, 2, 0, 3, 6, 0], [4, 2, 1, 3, 6, 0], [2, 0, 0, 3, 2, 1], [2, 0, 3, 4, 2, 1], [3, 2, 3, 4, 2, 1], [3, 5, 3, 4, 2, 1], [6, 3, 4, 2, 3, 1], [3, 0, 3, 5, 3, 1], [3, 1, 3, 5, 3, 1], [5, 2, 0, 3, 4, 1], [3, 4, 1, 3, 4, 1], [2, 0, 3, 6, 4, 1], [4, 2, 3, 6, 4, 1], [3, 6, 4, 1, 3, 2], [6, 1, 3, 5, 3, 2], [4, 3, 6, 5, 3, 2], [2, 3, 2, 3, 4, 2]]
def words (i : Fin 600) : List (Fin 7) := wordsData.getD i.val []
def repData : Array (Fin 25 × Fin 25) := #[(0, 0), (0, 1)]
def rep (i : Fin 2) := repData.getD i.val (0, 0)
def trData : Array (Array (Fin 2 × Fin 600)) := #[#[(0, 0), (1, 0), (1, 26), (1, 29), (1, 25), (1, 27), (1, 28), (1, 71), (1, 36), (1, 35), (1, 30), (1, 42), (1, 32), (1, 50), (1, 39), (1, 38), (1, 60), (1, 31), (1, 41), (1, 63), (1, 34), (1, 44), (1, 52), (1, 46), (1, 48)], #[(1, 1), (0, 1), (1, 49), (1, 43), (1, 33), (1, 92), (1, 59), (1, 106), (1, 99), (1, 119), (1, 141), (1, 70), (1, 154), (1, 79), (1, 47), (1, 80), (1, 45), (1, 72), (1, 112), (1, 51), (1, 40), (1, 37), (1, 61), (1, 62), (1, 176)], #[(1, 2), (1, 86), (0, 2), (1, 53), (1, 107), (1, 205), (1, 308), (1, 93), (1, 113), (1, 177), (1, 256), (1, 275), (1, 135), (1, 325), (1, 294), (1, 73), (1, 148), (1, 64), (1, 424), (1, 142), (1, 366), (1, 199), (1, 170), (1, 100), (1, 393)], #[(1, 5), (1, 83), (1, 56), (0, 5), (1, 89), (1, 368), (1, 218), (1, 103), (1, 173), (1, 202), (1, 76), (1, 145), (1, 426), (1, 67), (1, 151), (1, 259), (1, 194), (1, 328), (1, 138), (1, 278), (1, 208), (1, 180), (1, 116), (1, 96), (1, 289)], #[(1, 8), (1, 81), (1, 241), (1, 121), (0, 8), (1, 183), (1, 494), (1, 382), (1, 283), (1, 155), (1, 225), (1, 185), (1, 372), (1, 429), (1, 157), (1, 541), (1, 281), (1, 459), (1, 490), (1, 356), (1, 524), (1, 344), (1, 431), (1, 314), (1, 263)], #[(1, 3), (1, 230), (1, 74), (1, 257), (1, 206), (0, 3), (1, 171), (1, 65), (1, 136), (1, 94), (1, 108), (1, 394), (1, 143), (1, 295), (1, 178), (1, 87), (1, 200), (1, 149), (1, 276), (1, 309), (1, 54), (1, 101), (1, 346), (1, 326), (1, 114)], #[(1, 4), (1, 179), (1, 327), (1, 66), (1, 201), (1, 102), (0, 4), (1, 310), (1, 258), (1, 144), (1, 150), (1, 367), (1, 109), (1, 115), (1, 137), (1, 296), (1, 425), (1, 172), (1, 88), (1, 207), (1, 95), (1, 277), (1, 75), (1, 395), (1, 55)], #[(1, 222), (1, 476), (1, 231), (1, 240), (1, 452), (1, 24), (1, 516), (0, 24), (1, 338), (1, 408), (1, 496), (1, 537), (1, 534), (1, 561), (1, 414), (1, 523), (1, 520), (1, 447), (1, 574), (1, 553), (1, 445), (1, 563), (1, 347), (1, 341), (1, 354)], #[(1, 12), (1, 237), (1, 266), (1, 285), (1, 404), (1, 433), (1, 500), (1, 542), (0, 12), (1, 576), (1, 518), (1, 302), (1, 187), (1, 446), (1, 418), (1, 160), (1, 315), (1, 220), (1, 457), (1, 245), (1, 413), (1, 359), (1, 124), (1, 374), (1, 353)], #[(1, 11), (1, 479), (1, 358), (1, 495), (1, 486), (1, 232), (1, 348), (1, 186), (1, 461), (0, 11), (1, 453), (1, 159), (1, 284), (1, 301), (1, 409), (1, 373), (1, 564), (1, 244), (1, 265), (1, 539), (1, 417), (1, 123), (1, 432), (1, 526), (1, 384)], #[(1, 6), (1, 260), (1, 369), (1, 209), (1, 77), (1, 90), (1, 279), (1, 203), (1, 311), (1, 152), (0, 6), (1, 139), (1, 174), (1, 97), (1, 68), (1, 57), (1, 329), (1, 104), (1, 117), (1, 427), (1, 110), (1, 297), (1, 396), (1, 181), (1, 146)], #[(1, 17), (1, 221), (1, 389), (1, 483), (1, 271), (1, 165), (1, 519), (1, 321), (1, 251), (1, 487), (1, 405), (0, 17), (1, 581), (1, 593), (1, 536), (1, 466), (1, 340), (1, 362), (1, 474), (1, 130), (1, 568), (1, 499), (1, 305), (1, 422), (1, 193)], #[(1, 9), (1, 156), (1, 430), (1, 460), (1, 567), (1, 482), (1, 242), (1, 594), (1, 470), (1, 415), (1, 282), (1, 525), (0, 9), (1, 371), (1, 558), (1, 262), (1, 586), (1, 485), (1, 120), (1, 184), (1, 383), (1, 313), (1, 572), (1, 355), (1, 299)], #[(1, 21), (1, 226), (1, 407), (1, 219), (1, 532), (1, 550), (1, 401), (1, 522), (1, 517), (1, 512), (1, 235), (1, 535), (1, 351), (0, 21), (1, 441), (1, 449), (1, 538), (1, 212), (1, 339), (1, 345), (1, 455), (1, 334), (1, 398), (1, 411), (1, 548)], #[(1, 15), (1, 85), (1, 376), (1, 484), (1, 318), (1, 255), (1, 381), (1, 248), (1, 287), (1, 190), (1, 198), (1, 324), (1, 469), (1, 472), (0, 15), (1, 439), (1, 127), (1, 502), (1, 134), (1, 392), (1, 293), (1, 528), (1, 269), (1, 169), (1, 463)], #[(1, 14), (1, 189), (1, 223), (1, 501), (1, 527), (1, 227), (1, 375), (1, 434), (1, 488), (1, 450), (1, 126), (1, 577), (1, 317), (1, 286), (1, 342), (0, 14), (1, 162), (1, 268), (1, 419), (1, 360), (1, 247), (1, 386), (1, 554), (1, 462), (1, 543)], #[(1, 213), (1, 18), (1, 196), (1, 475), (1, 509), (1, 493), (1, 306), (1, 379), (1, 437), (1, 588), (1, 569), (1, 132), (1, 402), (1, 323), (1, 291), (1, 364), (0, 18), (1, 167), (1, 273), (1, 423), (1, 546), (1, 253), (1, 390), (1, 514), (1, 467)], #[(1, 7), (1, 140), (1, 217), (1, 312), (1, 428), (1, 280), (1, 105), (1, 210), (1, 69), (1, 111), (1, 175), (1, 182), (1, 153), (1, 58), (1, 261), (1, 118), (1, 78), (0, 7), (1, 298), (1, 204), (1, 147), (1, 91), (1, 330), (1, 370), (1, 98)], #[(1, 16), (1, 477), (1, 465), (1, 435), (1, 164), (1, 388), (1, 228), (1, 361), (1, 582), (1, 320), (1, 270), (1, 192), (1, 129), (1, 544), (1, 480), (1, 288), (1, 506), (1, 377), (0, 16), (1, 529), (1, 451), (1, 421), (1, 473), (1, 595), (1, 250)], #[(1, 216), (1, 22), (1, 481), (1, 508), (1, 552), (1, 560), (1, 444), (1, 557), (1, 498), (1, 589), (1, 571), (1, 337), (1, 442), (1, 331), (1, 584), (1, 575), (1, 549), (1, 497), (1, 583), (0, 22), (1, 403), (1, 491), (1, 515), (1, 507), (1, 598)], #[(1, 10), (1, 82), (1, 464), (1, 163), (1, 565), (1, 122), (1, 233), (1, 128), (1, 587), (1, 191), (1, 243), (1, 556), (1, 454), (1, 249), (1, 420), (1, 300), (1, 387), (1, 349), (1, 319), (1, 304), (0, 10), (1, 264), (1, 357), (1, 158), (1, 416)], #[(1, 84), (1, 13), (1, 471), (1, 363), (1, 188), (1, 239), (1, 125), (1, 316), (1, 436), (1, 131), (1, 378), (1, 246), (1, 272), (1, 252), (1, 385), (1, 545), (1, 303), (1, 229), (1, 290), (1, 166), (1, 322), (0, 13), (1, 267), (1, 195), (1, 161)], #[(1, 23), (1, 214), (1, 448), (1, 478), (1, 521), (1, 335), (1, 224), (1, 562), (1, 332), (1, 570), (1, 399), (1, 513), (1, 599), (1, 533), (1, 505), (1, 343), (1, 592), (1, 591), (1, 406), (1, 551), (1, 578), (1, 504), (0, 23), (1, 597), (1, 443)], #[(1, 19), (1, 215), (1, 238), (1, 234), (1, 380), (1, 559), (1, 168), (1, 133), (1, 350), (1, 336), (1, 365), (1, 292), (1, 438), (1, 197), (1, 254), (1, 555), (1, 307), (1, 530), (1, 468), (1, 274), (1, 458), (1, 410), (1, 391), (0, 19), (1, 540)], #[(1, 20), (1, 492), (1, 397), (1, 510), (1, 503), (1, 400), (1, 211), (1, 579), (1, 440), (1, 456), (1, 352), (1, 412), (1, 511), (1, 580), (1, 596), (1, 585), (1, 531), (1, 236), (1, 333), (1, 566), (1, 547), (1, 489), (1, 590), (1, 573), (0, 20)]]
def tr (x y : Fin 25) := (trData.getD x.val #[]).getD y.val (0, 0)
def sizes : Fin 2 → ℕ := ![1, 25]
def valuesData : Array (Array (Fin 25)) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
def values (i : Fin 2) (j : Fin (sizes i)) : Fin 25 := (valuesData.getD i.val #[]).getD j.val 0
def stabilizersData : Array (Array (Fin 600)) := #[#[25], #[0]]
def stabilizers (i : Fin 2) (j : Fin 1) : Fin 600 := (stabilizersData.getD i.val #[]).getD j.val 0

theorem transport_correct : ∀ x y,
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).1 = x ∧
    wordPerm genPerm (words (tr x y).2) (rep (tr x y).1).2 = y := by native_decide
theorem stabilizers_correct : ∀ i j,
    wordPerm genPerm (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
    wordPerm genPerm (words (stabilizers i j)) (rep i).2 = (rep i).2 := by native_decide
theorem values_complete : ∀ i x,
    (∀ j, wordPerm genPerm (words (stabilizers i j)) x = x) →
    ∃ a, values i a = x := by native_decide

abbrev Params := (i : Fin 2) → Fin (sizes i)
@[implicit_reducible] def fam (p : Params) : Magma (Fin 25) := family genPerm words tr sizes values p
@[implicit_reducible] def source : Magma (Fin 25) := ⟨sourceRow⟩
def pattern : Fin 1 → Bool := fun _ => false

theorem coverage (N : Magma (Fin 25)) (hg : ∀ i, N.IsEndo (genPerm i)) : ∃ p, fam p = N :=
  classification genPerm words rep tr sizes values stabilizers
    transport_correct stabilizers_correct values_complete N hg

theorem source_generators : ∀ i, source.IsEndo (genPerm i) := by native_decide
theorem source_pattern : Pattern source probePerm pattern := by native_decide

theorem target419 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation419 (Fin 25) (fam p) := by native_decide

theorem target617 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation617 (Fin 25) (fam p) := by native_decide

theorem target826 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation826 (Fin 25) (fam p) := by native_decide

theorem target1029 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1029 (Fin 25) (fam p) := by native_decide

theorem target1045 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1045 (Fin 25) (fam p) := by native_decide

theorem target1226 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1226 (Fin 25) (fam p) := by native_decide

theorem target1231 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1231 (Fin 25) (fam p) := by native_decide

theorem target1632 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1632 (Fin 25) (fam p) := by native_decide

theorem target1691 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation1691 (Fin 25) (fam p) := by native_decide

theorem target3306 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3306 (Fin 25) (fam p) := by native_decide

theorem target3353 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3353 (Fin 25) (fam p) := by native_decide

theorem target3459 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3459 (Fin 25) (fam p) := by native_decide

theorem target3518 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3518 (Fin 25) (fam p) := by native_decide

theorem target3724 : ∀ p : Params, Pattern (fam p) probePerm pattern → ¬ @Equation3724 (Fin 25) (fam p) := by native_decide

end Magma.Field25Index3Source4

open Magma.Field25Index3Source4

theorem Equation617_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law617.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target617 p hpattern ((@Law617.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation617_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation617_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target617._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation617_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation419_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law419.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target419 p hpattern ((@Law419.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation419_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation419_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target419._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation419_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation826_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law826.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target826 p hpattern ((@Law826.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation826_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation826_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target826._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation826_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation1029_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law1029.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1029 p hpattern ((@Law1029.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation1029_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1029_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1029._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1029_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation1045_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law1045.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1045 p hpattern ((@Law1045.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation1045_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1045_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1045._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1045_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation1226_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law1226.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1226 p hpattern ((@Law1226.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation1226_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1226_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1226._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1226_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation1231_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law1231.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1231 p hpattern ((@Law1231.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation1231_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1231_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1231._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1231_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation1632_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law1632.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1632 p hpattern ((@Law1632.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation1632_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1632_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1632._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1632_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation1691_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law1691.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target1691 p hpattern ((@Law1691.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation1691_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation1691_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target1691._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1691_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation3306_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law3306.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3306 p hpattern ((@Law3306.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation3306_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3306_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3306._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3306_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation3353_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law3353.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3353 p hpattern ((@Law3353.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation3353_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3353_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3353._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3353_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation3459_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law3459.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3459 p hpattern ((@Law3459.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation3459_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3459_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3459._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3459_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation3724_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law3724.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3724 p hpattern ((@Law3724.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation3724_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3724_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3724._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3724_not_structuralFromFin_Equation882_field25Index3Source4

theorem Equation3518_not_structuralFromFin_Equation882_field25Index3Source4 : ¬ Law3518.StructuralFromFin Law882 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin source genPerm probePerm pattern fam coverage
  · exact (@Law882.models_iff (Fin 25) source).mpr (by native_decide)
  · exact source_generators
  · exact source_pattern
  · intro p hp
    intro hpattern
    exact target3518 p hpattern ((@Law3518.models_iff (Fin 25) (fam p)).mp hp)

/-- info: 'Equation3518_not_structuralFromFin_Equation882_field25Index3Source4' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3518_not_structuralFromFin_Equation882_field25Index3Source4._native.native_decide.ax_1_1, gen_inverse._native.native_decide.ax_1_1, probe_inverse._native.native_decide.ax_1_1, source_generators._native.native_decide.ax_1_1, source_pattern._native.native_decide.ax_1_1, stabilizers_correct._native.native_decide.ax_1_1, target3518._native.native_decide.ax_1_1, transport_correct._native.native_decide.ax_1_1, values_complete._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3518_not_structuralFromFin_Equation882_field25Index3Source4

