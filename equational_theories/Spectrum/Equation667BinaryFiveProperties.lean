import equational_theories.Spectrum.Equation667BinaryFive
import equational_theories.Spectrum.Equation667Subclasses

/-! Structural properties of the binary five-point family. -/
namespace Spectrum.E667.BinaryFive

abbrev Constant (v : ZMod 5 → ZMod 2) : Prop := ∀ i, v i = v 0

/-- The cocycle vanishes precisely for constant binary data. -/
theorem cocycle_zero_iff (v : ZMod 5 → ZMod 2) :
    (∀ i j, cocycle v i j = 0) ↔ Constant v := by
  constructor
  · intro hc i
    have hi : 2 * (3 * i) - 0 = i := by ring_nf; reduce_mod_char
    have hh := hc 0 (3 * i)
    simp only [cocycle, hi] at hh
    linear_combination (norm := skip) hh
    ring_nf
    reduce_mod_char
  · intro hv i j
    simp only [cocycle, hv]
    ring_nf
    reduce_mod_char

/-- Squaring is a homomorphism exactly in the constant-data case. -/
theorem square_hom_iff (v : ZMod 5 → ZMod 2) :
    (∀ x y, op v (op v x y) (op v x y) = op v (op v x x) (op v y y)) ↔ Constant v := by
  rw [← cocycle_zero_iff]
  constructor
  · intro h i j
    have hh := congrArg Prod.snd (h (i, 0) (j, 0))
    simp only [square] at hh
    change (0 : ZMod 2) = 0 + 0 + cocycle v i j at hh
    simpa using hh.symm
  · intro hc x y
    rw [square v (op v x y), square v x, square v y]
    apply Prod.ext
    · rfl
    · change (0 : ZMod 2) = 0 + 0 + cocycle v x.1 y.1
      simp only [hc, add_zero]

/-- Exactly the constant-data members are commutative. -/
theorem commutative_iff_constant (v : ZMod 5 → ZMod 2) :
    (∀ x y, op v x y = op v y x) ↔ Constant v := by
  constructor
  · intro hc
    letI : Magma (ZMod 5 × ZMod 2) := ⟨op v⟩
    exact (square_hom_iff v).mp (square_hom_of_commutative (law v) hc)
  · intro hv x y
    have hc := (cocycle_zero_iff v).mpr hv
    apply Prod.ext
    · change base x.1 y.1 = base y.1 x.1
      simp only [base, add_comm]
    · change x.2 + y.2 + cocycle v x.1 y.1 = y.2 + x.2 + cocycle v y.1 x.1
      simp only [hc, add_comm]

/-- Exactly the constant-data members are medial. -/
theorem medial_iff_constant (v : ZMod 5 → ZMod 2) :
    (∀ x y z w, op v (op v x y) (op v z w) = op v (op v x z) (op v y w)) ↔
      Constant v := by
  constructor
  · intro hm
    exact (square_hom_iff v).mp (fun x y => hm x y x y)
  · intro hv x y z w
    have hc := (cocycle_zero_iff v).mpr hv
    apply Prod.ext
    · change base (base x.1 y.1) (base z.1 w.1) = base (base x.1 z.1) (base y.1 w.1)
      simp only [base]
      ring
    · simp only [op, hc, add_zero]
      ring

/-- Closure of the idempotents also characterizes constant data. -/
theorem idempotents_closed_iff (v : ZMod 5 → ZMod 2) :
    (∀ x y, op v x x = x → op v y y = y →
      op v (op v x y) (op v x y) = op v x y) ↔ Constant v := by
  constructor
  · intro h
    apply (cocycle_zero_iff v).mp
    intro i j
    have hi : op v (i, 0) (i, 0) = (i, 0) := square v _
    have hj : op v (j, 0) (j, 0) = (j, 0) := square v _
    have hh := (idempotent_iff v _).mp (h (i, 0) (j, 0) hi hj)
    simpa only [op, zero_add] using hh
  · intro hv x y hx hy
    rw [(square_hom_iff v).mpr hv, hx, hy]

/-- The projection onto the five-point base remains a homomorphism even
when squaring itself fails to be one. -/
theorem projection_hom (v : ZMod 5 → ZMod 2) (x y : ZMod 5 × ZMod 2) :
    (op v x y).1 = base x.1 y.1 := rfl

/-- Every member of the family has exactly five idempotents. -/
theorem idempotents_card (v : ZMod 5 → ZMod 2) :
    Nat.card {x : ZMod 5 × ZMod 2 // op v x x = x} = 5 := by
  let e : {x : ZMod 5 × ZMod 2 // op v x x = x} ≃ ZMod 5 := {
    toFun := fun x => x.val.1
    invFun := fun i => ⟨(i, 0), square v _⟩
    left_inv := fun x => Subtype.ext (Prod.ext rfl ((idempotent_iff v x.val).mp x.property).symm)
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact Nat.card_zmod 5

spectrum_assert square_hom_iff complete
spectrum_assert commutative_iff_constant complete
spectrum_assert medial_iff_constant complete
spectrum_assert idempotents_closed_iff complete
spectrum_assert idempotents_card complete
end Spectrum.E667.BinaryFive
