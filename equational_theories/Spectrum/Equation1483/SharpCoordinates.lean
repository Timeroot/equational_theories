import equational_theories.Spectrum.Equation1483.RankRigidity
import Mathlib.Data.Finite.Prod

/-! Saturation of the edge rank bound gives rectangular coordinates in E1483.
No unproved projector or rank-descent identity is assumed. -/

namespace Spectrum.E1483.SharpCoordinates

open RankRigidity

variable {G : Type*} [Magma G]

abbrev Col (b : G) := {v : G // ∃ x, x ◇ b = v}

/-- Even without finiteness, a sharp edge identifies its return fiber exactly. -/
theorem sharp_fiber (h : Equation1483 G) {a b : G}
    (hs : ∀ x, a ◇ (b ◇ x) = b) :
    {x : G | a ◇ x = b} = {x : G | ∃ z, b ◇ z = x} := by
  ext x
  constructor
  · intro hx
    have he := right_argument_in_row h a x
    rwa [hx] at he
  · rintro ⟨z, rfl⟩
    exact hs z

def coordinates (a b x : G) : Row a × Col b :=
  (⟨a ◇ x, x, rfl⟩, ⟨x ◇ b, x, rfl⟩)

theorem coordinates_injective (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b) : Function.Injective (coordinates a b) := by
  obtain ⟨z, rfl⟩ := hab
  intro x y he
  apply CentralDual.row_edge_pair_injective h a z
  exact congrArg (fun p : Row a × Col (a ◇ z) => (p.1.val, p.2.val)) he

theorem coordinates_bijective [Finite G] (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b)
    (hc : Nat.card G = Nat.card (Row a) * Nat.card (Row b)) :
    Function.Bijective (coordinates a b) := by
  apply (coordinates_injective h hab).bijective_of_nat_card_le
  rw [Nat.card_prod, ← Nat.card_congr (CentralDual.translationImageEquiv h b)]
  exact hc.ge

/-- Along an edge, multiplying the two coordinates recovers the element. -/
theorem multiply_coordinates (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b) (x : G) : (a ◇ x) ◇ (x ◇ b) = x := by
  obtain ⟨z, rfl⟩ := hab
  exact (h x a z).symm

/-- At equality in the rank bound, multiplication recovers every coordinate pair. -/
theorem coordinates_multiply [Finite G] (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b)
    (hc : Nat.card G = Nat.card (Row a) * Nat.card (Row b))
    (u : Row a) (v : Col b) : coordinates a b (u.val ◇ v.val) = (u, v) := by
  obtain ⟨x, hx⟩ := (coordinates_bijective h hab hc).2 (u, v)
  have hm := multiply_coordinates h hab x
  have hu : a ◇ x = u.val := congrArg (fun p : Row a × Col b => p.1.val) hx
  have hv : x ◇ b = v.val := congrArg (fun p : Row a × Col b => p.2.val) hx
  rw [hu, hv] at hm
  exact hm ▸ hx

/-- A saturated edge is sharp: every following product returns to its endpoint. -/
theorem sharp_left [Finite G] (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b)
    (hc : Nat.card G = Nat.card (Row a) * Nat.card (Row b)) (x : G) :
    a ◇ (b ◇ x) = b := by
  have he := congrArg (fun p : Row a × Col b => p.1.val)
    (coordinates_multiply h hab hc ⟨b, hab⟩ ⟨(b ◇ x) ◇ b, b ◇ x, rfl⟩)
  change a ◇ (b ◇ ((b ◇ x) ◇ b)) = b at he
  rwa [CentralDual.left_regular h b x] at he

/-- The same saturated edge is sharp on the other side. -/
theorem sharp_right [Finite G] (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b)
    (hc : Nat.card G = Nat.card (Row a) * Nat.card (Row b)) (x : G) :
    (x ◇ a) ◇ b = a := by
  have ha : ∃ z, z ◇ b = a := by
    obtain ⟨z, rfl⟩ := hab
    exact ⟨(a ◇ z) ◇ a, CentralDual.dual h a z a⟩
  have he := congrArg (fun p : Row a × Col b => p.2.val)
    (coordinates_multiply h hab hc ⟨a ◇ (x ◇ a), x ◇ a, rfl⟩ ⟨a, ha⟩)
  change ((a ◇ (x ◇ a)) ◇ a) ◇ b = a at he
  rwa [CentralDual.right_regular h a x] at he

/-- Every nonempty left fiber at the edge source has the neighbor's rank. -/
noncomputable def leftFiberEquiv [Finite G] (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b)
    (hc : Nat.card G = Nat.card (Row a) * Nat.card (Row b)) (u : Row a) :
    {x : G // a ◇ x = u.val} ≃ Col b where
  toFun x := ⟨x.val ◇ b, x.val, rfl⟩
  invFun v := ⟨u.val ◇ v.val, congrArg (fun p : Row a × Col b => p.1.val)
    (coordinates_multiply h hab hc u v)⟩
  left_inv x := by
    apply Subtype.ext
    have he := multiply_coordinates h hab x.val
    simpa only [x.property] using he
  right_inv v := by
    apply Subtype.ext
    exact congrArg (fun p : Row a × Col b => p.2.val)
      (coordinates_multiply h hab hc u v)

theorem fiber_card_left [Finite G] (h : Equation1483 G) {a b : G}
    (hab : ∃ z, a ◇ z = b)
    (hc : Nat.card G = Nat.card (Row a) * Nat.card (Row b)) (u : Row a) :
    Nat.card {x : G // a ◇ x = u.val} = Nat.card (Row b) := by
  rw [Nat.card_congr (leftFiberEquiv h hab hc u)]
  exact (Nat.card_congr (CentralDual.translationImageEquiv h b)).symm

/-- info: 'Spectrum.E1483.SharpCoordinates.sharp_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharp_left

end Spectrum.E1483.SharpCoordinates
