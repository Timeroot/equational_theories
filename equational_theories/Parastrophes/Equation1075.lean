import equational_theories.Parastrophes.Attributes
import equational_theories.ManuallyProved.Equation1075Idempotent
import equational_theories.Equations.All

/-! A countable E1075 counterexample to left bijectivity, and the relationship
between its row and column collisions. -/

namespace Parastrophes.Equation1075

variable {G : Type*} [Magma G]

/-- A collision in a row of an E1075 model also produces a collision in a column. -/
theorem column_collision_of_row (h : Equation1075 G) {a b c : G}
    (hc : a ◇ b = a ◇ c) :
    b ◇ ((a ◇ (a ◇ b)) ◇ a) = c ◇ ((a ◇ (a ◇ b)) ◇ a) := by
  rw [← h a b, hc, ← h a c]

/-- Right cancellation suffices for left bijectivity; finiteness is unnecessary. -/
theorem left_bijective_of_right_injective (h : Equation1075 G)
    (hr : ∀ z : G, Function.Injective (fun x => x ◇ z)) (a : G) :
    Function.Bijective (fun x => a ◇ x) := by
  constructor
  · intro b c hc
    exact hr _ (column_collision_of_row h hc)
  · intro x
    exact ⟨(x ◇ (x ◇ a)) ◇ x, (h x a).symm⟩

end Parastrophes.Equation1075

namespace Parastrophes.Catalogue

/-- The countable idempotent free-group construction preserves a row collision,
so E1075 does not force left bijectivity on arbitrary carriers. -/
@[parastrophe_result] theorem not_leftQuasigroup1075_all_collision :
    ¬ SideQuasigroupLaw .all Law1075 .left := by
  intro h
  obtain ⟨M,h1075,_,hn⟩ := Eq1075Free.countermodel
  have hQ := h (FreeGroup Nat) M trivial
    ((@Law1075.models_iff _ M).mpr h1075)
  exact hn (hQ 1).1

end Parastrophes.Catalogue
