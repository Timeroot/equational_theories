import equational_theories.Definability.E63Malcev
import Mathlib.Tactic.Group

/-!
# E125 with a regular group of automorphisms

The existing infinite E73 construction has operation `f(y*x⁻¹)*x` on a free
group. Every term interpretation preserves its right translations. This file
isolates the functional equation for an E125 operation of that form and proves
the bijectivity of all unary term operations. It makes no classification claim.
-/

namespace E63Family.Homogeneous

variable {G : Type*} [Group G]

def op (f : G → G) (x y : G) : G := f (y * x⁻¹) * x

theorem right_equivariant (f : G → G) (x y z : G) :
    op f (x * z) (y * z) = op f x y * z := by
  simp [op, mul_inv_rev, mul_assoc]

/-- Every operation invariant under the right regular action has this form. -/
theorem of_right_equivariant (m : G → G → G)
    (h : ∀ x y z, m (x * z) (y * z) = m x y * z) (x y : G) :
    m x y = op (m 1) x y := by
  simpa [op] using h 1 (y * x⁻¹) x

/-- Equivariance passes to every parameter-free magma term. -/
theorem term_right_equivariant {α : Type*} (f : G → G) (t : FreeMagma α)
    (v : α → G) (z : G) :
    @FreeMagma.evalInMagma α G ⟨op f⟩ (fun a => v a * z) t =
      @FreeMagma.evalInMagma α G ⟨op f⟩ v t * z := by
  induction t with
  | Leaf _ => rfl
  | Fork a b ha hb =>
    change op f _ _ = op f _ _ * z
    rw [ha, hb, right_equivariant]

/-- A single-variable functional equation is equivalent to the full E125 law. -/
theorem equation125_iff (f : G → G) :
    @Equation125 G ⟨op f⟩ ↔ ∀ x, f (f (f x)⁻¹ * f x) = x := by
  constructor
  · intro h x
    simpa [op] using (h x 1).symm
  · intro h x y
    change x = op f y (op f (op f y x) y)
    simp only [op, mul_inv_rev]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [h]
    simp

theorem bijective_f (f : G → G) (h : @Equation125 G ⟨op f⟩) : Function.Bijective f := by
  have hf := (equation125_iff f).mp h
  constructor
  · intro x y hxy
    calc
      x = f (f (f x)⁻¹ * f x) := (hf x).symm
      _ = f (f (f y)⁻¹ * f y) := by rw [hxy]
      _ = y := hf y
  · intro x
    exact ⟨f (f x)⁻¹ * f x, hf x⟩

theorem bijective_difference (f : G → G) (h : @Equation125 G ⟨op f⟩) :
    Function.Bijective (fun x => f x * x⁻¹) := by
  have h73 := @equation73_of_125 G ⟨op f⟩ h
  have hleft : Function.LeftInverse (fun x => f (f x)) (fun x => f x⁻¹ * x) := by
    intro x
    simpa [op] using (h73 x 1).symm
  have hright : Function.RightInverse (fun x => f (f x)) (fun x => f x⁻¹ * x) := by
    intro x
    simpa [op] using (@rotate_125 G ⟨op f⟩ h x 1)
  have hi : Function.Bijective (fun x : G => x⁻¹) := inv_involutive.bijective
  simpa only [Function.comp_def, inv_inv] using
    (show Function.Bijective (fun x => f x⁻¹ * x) from
      ⟨hleft.injective, hright.surjective⟩).comp hi

theorem diagonal_cycle (f : G → G) (h : @Equation125 G ⟨op f⟩) : f (f (f 1)) = 1 := by
  simpa [op] using (@equation73_of_125 G ⟨op f⟩ h 1 1).symm

/-- A unary term is left multiplication by its value at the identity. -/
theorem unary_term (f : G → G) (t : FreeMagma Unit) (x : G) :
    @FreeMagma.evalInMagma Unit G ⟨op f⟩ (fun _ => x) t =
      @FreeMagma.evalInMagma Unit G ⟨op f⟩ (fun _ => 1) t * x := by
  induction t with
  | Leaf _ => exact (one_mul x).symm
  | Fork a b ha hb =>
    change op f _ _ = op f _ _ * x
    rw [ha, hb, right_equivariant]

theorem unary_term_bijective (f : G → G) (t : FreeMagma Unit) :
    Function.Bijective (fun x => @FreeMagma.evalInMagma Unit G ⟨op f⟩ (fun _ => x) t) := by
  have he : (fun x => @FreeMagma.evalInMagma Unit G ⟨op f⟩ (fun _ => x) t) =
      fun x => @FreeMagma.evalInMagma Unit G ⟨op f⟩ (fun _ => 1) t * x :=
    funext (unary_term f t)
  rw [he]
  exact ⟨fun _ _ => mul_left_cancel, fun y =>
    ⟨(@FreeMagma.evalInMagma Unit G ⟨op f⟩ (fun _ => 1) t)⁻¹ * y, by simp⟩⟩

spectrum_assert equation125_iff complete
spectrum_assert of_right_equivariant complete
spectrum_assert term_right_equivariant complete
spectrum_assert bijective_f complete
spectrum_assert bijective_difference complete
spectrum_assert diagonal_cycle complete
spectrum_assert unary_term_bijective complete

end E63Family.Homogeneous
