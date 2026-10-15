import equational_theories.Equations.Eqns3000_3999

/-!
Elementary unary identities for E3342 and E3545. These hold on arbitrary
carriers; no finiteness, injectivity, or bounded order of the cube map is assumed.
They do not establish a definability arrow between the two laws.
-/

namespace CubeTwists

variable {G : Type*} (f : G → G → G)

def square (x : G) := f x x
def leftCube (x : G) := f x (square f x)
def rightCube (x : G) := f (square f x) x

/-- A twisted commutativity law makes the operation invariant under applying
its twist to both arguments. -/
theorem simultaneous (w : G → G) (h : ∀ x y, f x y = f y (w x)) (x y : G) :
    f (w x) (w y) = f x y :=
  ((h x y).trans (h y (w x))).symm

/-- In particular, the twist preserves each square fiber. -/
theorem square_twist (w : G → G) (h : ∀ x y, f x y = f y (w x)) (x : G) :
    square f (w x) = square f x := simultaneous f w h x x

/-- For E3342, the right cube fixes every value of the left cube. -/
theorem rightCube_leftCube
    (h : ∀ x y, f x y = f y (leftCube f x)) (x : G) :
    rightCube f (leftCube f x) = leftCube f x := by
  unfold rightCube
  rw [square_twist f (leftCube f) h x]
  exact (h x (square f x)).symm

/-- For E3545, the left cube is the second iterate of the right cube. -/
theorem leftCube_eq_rightCube_squared
    (h : ∀ x y, f x y = f y (rightCube f x)) (x : G) :
    leftCube f x = rightCube f (rightCube f x) := by
  change leftCube f x = f (square f (rightCube f x)) (rightCube f x)
  rw [square_twist f (rightCube f) h x]
  exact h x (square f x)

end CubeTwists
