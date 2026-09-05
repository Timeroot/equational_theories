import equational_theories.Equations.All
import equational_theories.Superposition

/-!
# The branch dichotomy of equation 692

`692` is `x = y ◇ (x ◇ ((z ◇ y) ◇ z))`. Attached to it is the unary term

    `B x := x ◇ (x ◇ x)`,

and the whole equational content of the law is carried by three facts about `B`, all consequences
of `692` alone: it is the value of the law-`14` expression,

    `y ◇ (x ◇ y) = B x`      (uniformly in `y`),

it absorbs into products, `B x ◇ y = x ◇ B y = B (B (x ◇ y))`, and it has order dividing three.
Equation `14` is `x = y ◇ (x ◇ y)`, so a model of `692` satisfies `14` exactly when `B = id`; and a
single fixed point of `B` already forces that. Hence every model of `692` is one of

* **branch A** — a model of `14`;
* **branch B** — one on which `B` is a fixed-point-free automorphism of order three.

Both branch conditions are sentences, which is what makes the split usable for definability.
`Set.Definable ∅` admits no parameters, so a case analysis is legal only when each side is
parameter free; `¬ (∀ u, B u = u)` on its own supplies a witness `u` with `B u ≠ u`, but
`equation14_of_rot692_fixed` turns that witness back into the sentence `∀ u, B u ≠ u`.

Since `B` is an automorphism, its orbits are a congruence, the quotient by `⟨B⟩` is a model of `14`,
and a branch-B model is a `ℤ/3`-cover of a `14`-model. `Definability/Shift692.lean` carries the
smallest such cover and `Definability/Aff692.lean` an eighty-one element affine one.
-/

namespace Magma

variable {G : Type*} [Magma G]

/-- The rotation of a model of `692`: `B x = x ◇ (x ◇ x)`. It is an automorphism of order dividing
three, and it is the identity exactly when the model satisfies equation `14`. -/
def rot692 [Magma G] (x : G) : G := x ◇ (x ◇ x)

/-- `y ◇ (x ◇ y) = B x`: the law-`14` expression does not depend on `y`, and its value is the
rotation. -/
theorem rot692_eq (h : Equation692 G) (x y : G) : y ◇ (x ◇ y) = rot692 x := by
  have eq6 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq6 eq6
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1)) ◇ X0) = X3 :=
    superpose eq6 eq9
  have eq206 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq9 eq12
  have eq625 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X3)) := superpose eq206 eq9
  exact eq625 x y x

/-- `(y ◇ B x) ◇ y = x`: the rotation is undone by any right multiplication sandwich. This is
`Definability/DFO.lean`'s right cancellation, rewritten through `rot692_eq`. -/
theorem rot692_sandwich (h : Equation692 G) (x y : G) : (y ◇ rot692 x) ◇ y = x := by
  have eq6 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq6 eq6
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1)) ◇ X0) = X3 :=
    superpose eq6 eq9
  have eq206 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq9 eq12
  exact eq206 x y x

/-- The rotation is injective. -/
theorem rot692_inj (h : Equation692 G) : Function.Injective (rot692 (G := G)) := by
  intro a b hab
  have ha := rot692_sandwich h a a
  have hb := rot692_sandwich h b a
  rw [hab] at ha
  exact ha.symm.trans hb

/-- `B x ◇ y = B (B (x ◇ y))`: the rotation absorbs into a product from the left. -/
theorem rot692_op_left (h : Equation692 G) (x y : G) :
    rot692 x ◇ y = rot692 (rot692 (x ◇ y)) := by
  have e14 (u v : G) : v ◇ (u ◇ v) = rot692 u := rot692_eq h u v
  have hc (u v : G) : (v ◇ rot692 u) ◇ v = u := rot692_sandwich h u v
  have h692 (u v w : G) : v ◇ (u ◇ ((w ◇ v) ◇ w)) = u := (h u v w).symm
  grind (config := { splits := 24, ematch := 14, instances := 8000, gen := 16 })

/-- `x ◇ B y = B (B (x ◇ y))`: the rotation absorbs into a product from the right. -/
theorem rot692_op_right (h : Equation692 G) (x y : G) :
    x ◇ rot692 y = rot692 (rot692 (x ◇ y)) := by
  have e14 (u v : G) : v ◇ (u ◇ v) = rot692 u := rot692_eq h u v
  have hc (u v : G) : (v ◇ rot692 u) ◇ v = u := rot692_sandwich h u v
  have h692 (u v w : G) : v ◇ (u ◇ ((w ◇ v) ◇ w)) = u := (h u v w).symm
  grind (config := { splits := 24, ematch := 14, instances := 8000, gen := 16 })

/-- `B³ = id`. Absorbing `B` out of `x ◇ (B x ◇ x)` in the two possible orders gives `B⁵ = B²`,
and `B` is injective. -/
theorem rot692_cube (h : Equation692 G) (x : G) : rot692 (rot692 (rot692 x)) = x := by
  have h1 : x ◇ (rot692 x ◇ x) = rot692 (rot692 x) := rot692_eq h (rot692 x) x
  have h2 : rot692 x ◇ x = rot692 (rot692 (x ◇ x)) := rot692_op_left h x x
  have h3 : x ◇ rot692 (rot692 (x ◇ x))
      = rot692 (rot692 (x ◇ rot692 (x ◇ x))) := rot692_op_right h x (rot692 (x ◇ x))
  have h4 : x ◇ rot692 (x ◇ x) = rot692 (rot692 (rot692 x)) := rot692_op_right h x (x ◇ x)
  have key : rot692 (rot692 x) = rot692 (rot692 (rot692 (rot692 (rot692 x)))) :=
    calc rot692 (rot692 x)
        = x ◇ (rot692 x ◇ x) := h1.symm
      _ = x ◇ rot692 (rot692 (x ◇ x)) := by rw [h2]
      _ = rot692 (rot692 (x ◇ rot692 (x ◇ x))) := h3
      _ = rot692 (rot692 (rot692 (rot692 (rot692 x)))) := by rw [h4]
  exact rot692_inj h (rot692_inj h key.symm)

/-- `B` is an automorphism. -/
theorem rot692_hom (h : Equation692 G) (x y : G) :
    rot692 (x ◇ y) = rot692 x ◇ rot692 y := by
  rw [rot692_op_left h x (rot692 y), rot692_op_right h x y, rot692_cube h (x ◇ y)]

/-- A single fixed point of `B` forces `B = id`, that is, equation `14`. -/
theorem equation14_of_rot692_fixed (h : Equation692 G) {a : G} (ha : rot692 a = a) :
    Equation14 G := by
  have key (x : G) : (a ◇ a) ◇ (x ◇ (a ◇ a)) = x := by
    have := (h x (a ◇ a) a).symm
    rwa [show a ◇ (a ◇ a) = a from ha] at this
  intro x y
  rw [rot692_eq h x y, ← rot692_eq h x (a ◇ a), key x]

/-- **The branch dichotomy.** A model of `692` either satisfies `14`, or its rotation is
fixed-point free. Both alternatives are sentences, so the split is available inside a definability
argument, where parameters are not. -/
theorem branch692 (h : Equation692 G) : Equation14 G ∨ ∀ x : G, rot692 x ≠ x := by
  by_cases hf : ∃ a : G, rot692 a = a
  · exact Or.inl (equation14_of_rot692_fixed h hf.choose_spec)
  · exact Or.inr fun x hx => hf ⟨x, hx⟩

/-- Branch A is exactly `B = id`. -/
theorem equation14_iff_rot692_id (h : Equation692 G) :
    Equation14 G ↔ ∀ x : G, rot692 x = x := by
  refine ⟨fun h14 x => ?_, fun hr x y => ?_⟩
  · rw [← rot692_eq h x x, ← h14 x x]
  · rw [rot692_eq h x y, hr x]

end Magma
