import equational_theories.Spectrum.SmallOrders.Chain

/-! Restrictions on the squaring permutation in finite E1110 magmas. -/
namespace Spectrum.E1110

variable {A : Type*} [Finite A] {f : A → A → A}

/-- Squaring in a finite E1110 magma has no cycle of length two. -/
theorem square_two_cycle (h : SmallOrders.Holds .e1110 f)
    {a b : A} (ha : f a a = b) (hb : f b b = a) : a = b := by
  have he := h a b
  change f b (f (f b (f a a)) b) = a at he
  rw [ha, hb] at he
  have hab : f a b = b := (SmallOrders.left_bijective h b).1 (he.trans hb.symm)
  exact ((SmallOrders.left_bijective h a).1 (hab.trans ha.symm)).symm

/-- A point fixed by the square of the squaring map is already idempotent. -/
theorem square_square_eq_iff (h : SmallOrders.Holds .e1110 f) (a : A) :
    f (f a a) (f a a) = a ↔ f a a = a := by
  constructor
  · intro ha
    exact (square_two_cycle h rfl ha).symm
  · intro ha
    rw [ha, ha]

end Spectrum.E1110
