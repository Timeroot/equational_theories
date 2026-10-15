import equational_theories.Spectrum.SmallOrders.CaseAssembly
import equational_theories.Spectrum.SmallOrders.Encoding

/-! The thirteen orderings of six possible cycle types, with explicit
permutations sending each ordering to its representative. All inverse and
conjugacy equations are checked by kernel reduction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.CanonicalData
abbrev Row := Fin 12 → Fin 12
private def rowData : Array (Array (Fin 12)) := #[
  #[0, 2, 3, 1, 5, 6, 4, 8, 9, 10, 11, 7],
  #[0, 2, 3, 1, 5, 6, 7, 4, 9, 10, 11, 8],
  #[0, 2, 3, 1, 5, 6, 7, 8, 4, 10, 11, 9],
  #[0, 2, 3, 1, 5, 6, 7, 8, 9, 10, 11, 4],
  #[0, 2, 3, 4, 1, 6, 7, 5, 9, 10, 11, 8],
  #[0, 2, 3, 4, 1, 6, 7, 8, 5, 10, 11, 9],
  #[0, 2, 3, 4, 1, 6, 7, 8, 9, 10, 11, 5],
  #[0, 2, 3, 4, 5, 1, 7, 8, 6, 10, 11, 9],
  #[0, 2, 3, 4, 5, 1, 7, 8, 9, 10, 11, 6],
  #[0, 2, 3, 4, 5, 6, 1, 8, 9, 10, 11, 7],
  #[0, 2, 3, 4, 5, 6, 7, 1, 9, 10, 11, 8],
  #[0, 2, 3, 4, 5, 6, 7, 8, 1, 10, 11, 9],
  #[0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1]]
def row (i : Fin 13) : Row := fun j => rowData[i.val]![j.val]!
private def repData : Array (Fin 13) := #[0, 1, 3, 6, 8, 12]
def representative (j : Fin 6) : Fin 13 := repData[j.val]!
private def targetData : Array (Fin 6) := #[0, 1, 0, 2, 1, 1, 3, 0, 4, 4, 3, 2, 5]
def target (i : Fin 13) : Fin 6 := targetData[i.val]!
private def sigmaData : Array (Array (Fin 12)) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 7, 8, 9, 10, 11, 4, 5, 6],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 4, 5, 6, 7, 1, 2, 3, 8, 9, 10, 11],
  #[0, 4, 5, 6, 7, 8, 9, 10, 11, 1, 2, 3],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 7, 8, 9, 10, 11, 1, 2, 3, 4, 5, 6],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 6, 7, 8, 9, 10, 11, 1, 2, 3, 4, 5],
  #[0, 5, 6, 7, 8, 9, 10, 11, 1, 2, 3, 4],
  #[0, 4, 5, 6, 7, 8, 9, 10, 11, 1, 2, 3],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
private def tauData : Array (Array (Fin 12)) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 1, 2, 3, 9, 10, 11, 4, 5, 6, 7, 8],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 5, 6, 7, 1, 2, 3, 4, 8, 9, 10, 11],
  #[0, 9, 10, 11, 1, 2, 3, 4, 5, 6, 7, 8],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 6, 7, 8, 9, 10, 11, 1, 2, 3, 4, 5],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  #[0, 7, 8, 9, 10, 11, 1, 2, 3, 4, 5, 6],
  #[0, 8, 9, 10, 11, 1, 2, 3, 4, 5, 6, 7],
  #[0, 9, 10, 11, 1, 2, 3, 4, 5, 6, 7, 8],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
def sigma (i : Fin 13) (x : Fin 12) : Fin 12 := sigmaData[i.val]![x.val]!
def tau (i : Fin 13) (x : Fin 12) : Fin 12 := tauData[i.val]![x.val]!

theorem maps_checked : ∀ i : Fin 13,
    (∀ x, tau i (sigma i x) = x) ∧ (∀ x, sigma i (tau i x) = x) ∧
    sigma i 0 = 0 ∧
    (∀ y, sigma i (row i (tau i y)) = row (representative (target i)) y) := by
  decide +kernel

theorem chain_checked : ∀ i : Fin 6, ∀ y : Fin 12,
    (row (representative i) y).val ≤ y.val + 1 := by decide +kernel

def permutation (i : Fin 13) : Equiv.Perm (Fin 12) where
  toFun := sigma i
  invFun := tau i
  left_inv := (maps_checked i).1
  right_inv := (maps_checked i).2.1

theorem zero_fixed (i : Fin 13) : permutation i 0 = 0 := (maps_checked i).2.2.1

theorem conjugates (i : Fin 13) (y : Fin 12) :
    permutation i (row i ((permutation i).symm y)) =
      row (representative (target i)) y := (maps_checked i).2.2.2 y

end Spectrum.E1076.OrderTwelve.CanonicalData
