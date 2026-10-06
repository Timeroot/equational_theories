import equational_theories.Spectrum.Equation667883Small.Basic

/-! Involutive automorphisms act on E667 operations by twisting their outputs.
The construction preserves commutativity and mediality, but its fixed points
can change the idempotents. No finiteness assumption is needed. -/
namespace Spectrum.E667.AutomorphismTwist

variable {Q : Type*} [Magma Q] (J : Q → Q)

def op (x y : Q) : Q := J (x ◇ y)

variable (hJ : Function.Involutive J)
    (hm : ∀ x y, J (x ◇ y) = J x ◇ J y)
include hJ hm

/-- Twisting any E667 magma by an involutive automorphism preserves E667. -/
theorem law (h : Equation667 Q) : @Equation667 Q ⟨op J⟩ := by
  have hj (x) : J (J x) = x := hJ x
  intro x y
  change x = J (y ◇ J (x ◇ J (J (x ◇ x) ◇ y)))
  simpa only [hm, hj] using h x (J y)

omit hJ hm in
/-- For an idempotent input the square map of the twist is exactly J. -/
theorem square (hi : ∀ x : Q, x ◇ x = x) (x : Q) : op J x x = J x := by
  simp only [op, hi]

/-- An idempotent E63 magma and an involutive automorphism give an E667 magma. -/
theorem of_idempotent_e63 (h : Equation63 Q) (hi : ∀ x : Q, x ◇ x = x) :
    @Equation667 Q ⟨op J⟩ := by
  apply law J hJ hm
  intro x y
  simpa only [hi] using h x y

/-- Conversely, an involutive square map which preserves multiplication can
be removed to obtain an idempotent E63 operation. -/
theorem untwist (h : Equation667 Q)
    (hd : ∀ x : Q, x ◇ x = J x) :
    @Equation63 Q ⟨op J⟩ ∧ ∀ x : Q, op J x x = x := by
  have hi (x : Q) : op J x x = x := by
    change J (x ◇ x) = x
    rw [hd]
    exact hJ x
  refine ⟨?_, hi⟩
  intro x y
  have hh := law J hJ hm h x y
  change x = op J y (op J x (op J (op J x x) y)) at hh
  simpa only [hi] using hh

omit hm in
/-- An injective output twist preserves and reflects commutativity. -/
theorem commutative_iff :
    (∀ x y, op J x y = op J y x) ↔ ∀ x y : Q, x ◇ y = y ◇ x := by
  constructor
  · intro hc x y
    exact hJ.injective (hc x y)
  · intro hc x y
    exact congrArg J (hc x y)

/-- Under an involutive automorphism, both sides of mediality lose their
outer twists. Nonmedial examples therefore stay nonmedial. -/
theorem medial_iff :
    (∀ x y z w, op J (op J x y) (op J z w) = op J (op J x z) (op J y w)) ↔
      ∀ x y z w : Q, (x ◇ y) ◇ (z ◇ w) = (x ◇ z) ◇ (y ◇ w) := by
  have hj (x) : J (J x) = x := hJ x
  simp only [op, hm, hj]

spectrum_assert law complete
spectrum_assert of_idempotent_e63 complete
spectrum_assert untwist complete
end Spectrum.E667.AutomorphismTwist
