import equational_theories.Definability.Homogeneous1516.Bridge
import equational_theories.Definability.Homogeneous1516.PowerReduction
import equational_theories.Definability.Homogeneous1516.Cases.S2
import equational_theories.Definability.Homogeneous1516.Cases.S4
import equational_theories.Definability.Homogeneous1516.Cases.S7
import equational_theories.Definability.Homogeneous1516.Cases.S12

/-! Complete homogeneous E1516 classification over F₂₉: every such operation
is idempotent. Four LRAT refutations and an algebraic involution argument
exclude all nonidentity diagonal multipliers, via power conjugation. -/
namespace Definability.Homogeneous1516
open GLTwo1516 Refutation
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

theorem representatives_excluded (p : ZMod 29 → ZMod 29 → ZMod 29)
    (hp : Homogeneous p) (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) :
    ¬ Representative (p 1 1) := by
  rintro (hs | hs | hs | hs | hs)
  · exact no_homogeneous_of_unsat 2 unsat2 p hp hlaw hs
  · exact no_homogeneous_of_unsat 4 unsat4 p hp hlaw hs
  · exact no_homogeneous_of_unsat 7 unsat7 p hp hlaw hs
  · exact no_homogeneous_of_unsat 12 unsat12 p hp hlaw hs
  · exact square_ne_neg_one hp (by decide) hlaw (hs.trans (by decide))

/-- This discharges the classification hypothesis of GLTwo1516.not_definableFromFin. -/
theorem classification (p : ZMod 29 → ZMod 29 → ZMod 29)
    (hp : Homogeneous p) (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) :
    p 1 1 = 1 :=
  diagonal_one_of_representatives_excluded representatives_excluded p hp hlaw
    (square_ne_zero hp (by decide) hlaw)

theorem idempotent (p : ZMod 29 → ZMod 29 → ZMod 29)
    (hp : Homogeneous p) (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) :
    ∀ x, p x x = x := by
  intro x
  rw [diagonal hp (by decide), classification p hp hlaw, one_mul]

spectrum_assert classification complete
spectrum_assert idempotent complete

end Definability.Homogeneous1516
