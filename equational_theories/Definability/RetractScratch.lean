import equational_theories.Equations.All
import equational_theories.Superposition
import Mathlib.Tactic

variable {G : Type} [Magma G] (e v : G → G)

-- 546 -> 3675 :  w a b = v (e a ◇ e b)
example
    (hsrc : ∀ x y z : G, x = y ◇ (z ◇ (x ◇ (z ◇ y))))
    (heh : ∀ x y : G, e (x ◇ y) = e x ◇ e y)
    (hvh : ∀ x y : G, v (x ◇ y) = v x ◇ v y)
    (hee : ∀ x : G, e (e x) = e x)
    (hve : ∀ x : G, v (e x) = e (v x))
    (huve : ∀ x : G, v (e x) ◇ v (e x) = e x)
    (hvue : ∀ x : G, v (e x ◇ e x) = e x)
    (x y : G) :
    v (e x ◇ e x) = v (e (v (e y ◇ e x)) ◇ e (v (e x ◇ e y))) := by
  grind
