import equational_theories.Definability.Central1483Constant
import equational_theories.Definability.Central1483Translations

/-! Elementary identities at a constant row of an E1483 magma. -/

namespace Spectrum.E1483.Constant

variable {G : Type*} [Magma G] (h : Equation1483 G) (zero one : G)
  (hzero : ∀ t : G, zero ◇ t = one)

include h hzero

theorem left_inverse (x : G) : one ◇ (x ◇ one) = x := by
  simpa only [hzero] using (h x zero zero).symm

theorem one_square : one ◇ one = zero := by
  simpa only [hzero] using left_inverse h zero one hzero zero

theorem one_zero : one ◇ zero = one := by
  have he := left_inverse h zero one hzero one
  rwa [one_square h zero one hzero] at he

theorem constant_column (x : G) : x ◇ zero = one := by
  have he : (x ◇ zero) ◇ one = zero := by
    simpa only [hzero] using (h zero x zero).symm
  calc
    x ◇ zero = one ◇ ((x ◇ zero) ◇ one) :=
      (left_inverse h zero one hzero (x ◇ zero)).symm
    _ = one ◇ zero := congrArg (one ◇ ·) he
    _ = one := one_zero h zero one hzero

theorem right_inverse (x : G) : (one ◇ x) ◇ one = x := by
  simpa only [hzero, constant_column h zero one hzero] using
    CentralDual.dual h x zero zero

theorem constant_row_unique (b c : G) (hb : ∀ t : G, b ◇ t = c) : b = zero := by
  have hc : c = one := (hb zero).symm.trans (constant_column h zero one hzero b)
  calc
    b = one ◇ (b ◇ one) := (left_inverse h zero one hzero b).symm
    _ = one ◇ one := by rw [hb, hc]
    _ = zero := one_square h zero one hzero

omit h hzero in
/-- The order-three automorphism used to remove the twist. -/
def twist (x : G) : G := one ◇ (one ◇ x)

theorem twist_mul (x y : G) :
    twist one (x ◇ y) = twist one x ◇ twist one y :=
  (CentralConstant.left_square_hom h zero one hzero x y).symm

theorem twist_three (x : G) : twist one (twist one (twist one x)) = x :=
  CentralConstant.left_six h zero one hzero x

theorem twist_zero : twist one zero = zero := by
  simp only [twist, one_zero h zero one hzero, one_square h zero one hzero]

theorem twist_one : twist one one = one := by
  simp only [twist, one_square h zero one hzero, one_zero h zero one hzero]

end Spectrum.E1483.Constant
