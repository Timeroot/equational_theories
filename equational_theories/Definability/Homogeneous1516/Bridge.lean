import equational_theories.Definability.Homogeneous1516.Normalization
import equational_theories.Definability.Homogeneous1516.Encoding

/-! Algebraic soundness bridge from homogeneous E1516 models to the finite CNF. -/

namespace Definability.Homogeneous1516

open GLTwo1516

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

theorem conditions_of_normalized {f g : ZMod 29 → ZMod 29} {c s : ZMod 29}
    (h : Normalized f g c s) : Encoding.Conditions f c s where
  bijective := h.bijective
  c_ne_zero := h.c_ne_zero
  f_zero_ne_zero := h.f_zero_ne_zero
  f_one := h.f_one
  zero_right := h.zero_right_apply
  zero_left := h.zero_left_inv
  main := h.main_apply
  right_zero := h.profile_ne
  right_unique := h.profile_injective

/-- A checked refutation of the finite formula excludes the corresponding
square multiplier in every homogeneous E1516 operation. -/
theorem no_homogeneous_of_unsat (s : ZMod 29) (hn : (Encoding.natFormula s).Unsat)
    (p : ZMod 29 → ZMod 29 → ZMod 29) (hp : Homogeneous p)
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) (hs : p 1 1 = s) : False := by
  obtain ⟨g, hg⟩ := exists_normalized hp (by decide) hlaw
  have hc := conditions_of_normalized hg
  rw [hs] at hc
  exact Encoding.no_conditions s hn (p 1) (p 0 1) hc

/-- info: 'Definability.Homogeneous1516.conditions_of_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditions_of_normalized

/-- info: 'Definability.Homogeneous1516.no_homogeneous_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_homogeneous_of_unsat

end Definability.Homogeneous1516
