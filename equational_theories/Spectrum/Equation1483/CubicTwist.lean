import equational_theories.Equations.All

/-! E1483 is preserved by twisting the two inputs by opposite powers of a
cubic automorphism. Mixed translations are unchanged apart from their parameters. -/
namespace Spectrum.E1483.CubicTwist

variable {G : Type*} (f : G → G → G) (φ : G → G)
  (hmul : ∀ x y, φ (f x y) = f (φ x) (φ y))
  (hthree : ∀ x, φ (φ (φ x)) = x)

def operation (x y : G) : G := f (φ (φ x)) (φ y)

include hmul hthree in
/-- Cubic automorphic isotopy preserves E1483. -/
theorem lawful (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∀ x y z, operation f φ (operation f φ y x)
      (operation f φ x (operation f φ y z)) = x := by
  intro x y z
  simp only [operation, hmul, hthree]
  exact h x (φ y) z

include hmul hthree in
/-- A cubic twist of an E168 operation is still central. -/
theorem central (h : ∀ x y z, f (f y x) (f x z) = x) :
    ∀ x y z, operation f φ (operation f φ y x) (operation f φ x z) = x := by
  intro x y z
  simp only [operation, hmul, hthree]
  exact h x (φ y) (φ (φ z))

include hmul hthree in
/-- The mixed projector changes only its two parameters. -/
theorem mixed (a b t : G) :
    operation f φ a (operation f φ t b) =
      f (φ (φ a)) (f t (φ (φ b))) := by
  change f (φ (φ a)) (φ (f (φ (φ t)) (φ b))) = f (φ (φ a)) (f t (φ (φ b)))
  exact congrArg (f (φ (φ a))) ((hmul (φ (φ t)) (φ b)).trans
    (congrArg (fun x => f x (φ (φ b))) (hthree t)))

include hthree in
/-- Applying the same cubic twist three times recovers the original operation. -/
theorem operation_three (x y : G) :
    operation (operation (operation f φ) φ) φ x y = f x y := by
  simp only [operation, hthree]

/-- info: 'Spectrum.E1483.CubicTwist.lawful' does not depend on any axioms -/
#guard_msgs in
#print axioms lawful

/-- info: 'Spectrum.E1483.CubicTwist.mixed' does not depend on any axioms -/
#guard_msgs in
#print axioms mixed

end Spectrum.E1483.CubicTwist
