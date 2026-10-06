import equational_theories.Spectrum.Equation667GroupConstructions
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Hom.End

/-! The exact affine equations for E667, and existence of an idempotent
when the finite abelian carrier has order coprime to ten. -/
namespace Spectrum.E667.AffineStructure
variable {A : Type*} [AddCommGroup A]

def op (f g : AddMonoid.End A) (c : A) (x y : A) := f x + g y + c

/-- E667 forces the two linear coefficients to be related, even if their
commutativity was not assumed. -/
theorem left_coefficient (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) (y : A) : f y = -g (g (g y)) := by
  have h0 := h 0 0
  have hy := h 0 y
  change 0 = op f g c 0 (op f g c 0 (op f g c (op f g c 0 0) 0)) at h0
  change 0 = op f g c y (op f g c 0 (op f g c (op f g c 0 0) y)) at hy
  simp only [op, map_zero, zero_add, add_zero, map_add] at h0 hy
  apply eq_neg_iff_add_eq_zero.mpr
  have he : f y + g (g (g y)) + (g (g (f c)) + g (g c) + g c + c) = 0 := by
    calc
      _ = f y + g (g (f c + g y + c) + c) + c := by simp only [map_add]; abel
      _ = 0 := by simpa only [map_add] using hy.symm
  have hz : g (g (f c)) + g (g c) + g c + c = 0 := by
    simpa only [map_add] using h0.symm
  simpa only [hz, add_zero] using he

def normalizedOp (g : AddMonoid.End A) (c : A) := op (-(g^3)) g c

def P (g : AddMonoid.End A) : AddMonoid.End A := g^8-g^6-g^4-1
def K (g : AddMonoid.End A) : AddMonoid.End A := -g^5+g^2+g+1
def H (g : AddMonoid.End A) : AddMonoid.End A := g^3-g+1

theorem normalized (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) : f = -(g^3) := by
  apply AddMonoidHom.ext
  intro y
  exact left_coefficient f g c h y

@[simp] theorem end_mul_apply (f g : AddMonoid.End A) (x : A) : (f*g) x = f (g x) := rfl
@[simp] theorem end_one_apply (x : A) : (1 : AddMonoid.End A) x = x := rfl

@[simp] theorem end_add_apply (f g : AddMonoid.End A) (x : A) : (f+g) x = f x+g x := rfl
@[simp] theorem end_sub_apply (f g : AddMonoid.End A) (x : A) : (f-g) x = f x-g x := rfl
@[simp] theorem end_neg_apply (f : AddMonoid.End A) (x : A) : (-f) x = -f x := rfl

/-- Direct symbolic expansion eliminates y and isolates two polynomial conditions. -/
theorem expansion (g : AddMonoid.End A) (c x y : A) :
    normalizedOp g c y (normalizedOp g c x
      (normalizedOp g c (normalizedOp g c x x) y)) = x + P g x + K g c := by
  simp only [normalizedOp, op, P, K, pow_succ, pow_zero, end_mul_apply,
    end_one_apply, end_neg_apply, end_sub_apply,
    end_add_apply, map_add, map_neg]
  abel

theorem law_iff (g : AddMonoid.End A) (c : A) :
    @Equation667 A ⟨normalizedOp g c⟩ ↔ P g = 0 ∧ K g c = 0 := by
  constructor
  · intro h
    have hh (x y : A) : x = x + P g x + K g c := (h x y).trans (expansion g c x y)
    have hk : K g c = 0 := by simpa only [map_zero, zero_add] using (hh 0 0).symm
    refine ⟨?_,hk⟩
    apply AddMonoidHom.ext
    intro x
    have hx := hh x 0
    rw [hk, add_zero] at hx
    exact (add_left_cancel (show x + P g x = x + 0 by simpa using hx.symm))
  · rintro ⟨hp,hk⟩ x y
    change x = normalizedOp g c y (normalizedOp g c x
      (normalizedOp g c (normalizedOp g c x x) y))
    rw [expansion, hp, hk]
    simp

theorem idempotent_iff (g : AddMonoid.End A) (c x : A) :
    normalizedOp g c x x = x ↔ H g x = c := by
  have he : H g x = x - normalizedOp g c x x + c := by
    simp only [H, normalizedOp, op, end_add_apply,
      end_sub_apply, end_neg_apply, end_one_apply]
    abel
  constructor
  · intro hh; rw [he, hh]; abel
  · intro hh
    have hx : normalizedOp g c x x = x - H g x + c := by rw [he]; abel
    rw [hx, hh]; abel

/-- An integral Bézout identity: the obstruction to removing the constant
is supported only at primes two and five. -/
theorem bezout (g : AddMonoid.End A) :
    H g * (-2*g^4-g^3+2*g^2+3*g+6) + (-2*g^2-g+4)*K g = 10 := by
  dsimp [H, K]
  noncomm_ring
  norm_num

/-- The scalar condition K(g)c=0 guarantees an idempotent after division by ten. -/
theorem idempotent_of_coprime (g : AddMonoid.End A) (c : A)
    (hk : K g c = 0) (hn : (Nat.card A).Coprime 10) :
    ∃ x, normalizedOp g c x x = x := by
  have hbij : Function.Bijective (fun x : A => (10 : ℕ) • x) := hn.nsmul_right_bijective
  obtain ⟨d,hd⟩ := hbij.surjective c
  change (10 : ℕ) • d = c at hd
  have hkd : K g d = 0 := by
    apply hbij.injective
    calc
      (10 : ℕ) • K g d = K g ((10 : ℕ) • d) := (map_nsmul (K g) 10 d).symm
      _ = 0 := by rw [hd, hk]
      _ = (10 : ℕ) • (0 : A) := by simp
  let R : AddMonoid.End A := -2*g^4-g^3+2*g^2+3*g+6
  refine ⟨R d, (idempotent_iff g c (R d)).mpr ?_⟩
  have hb := congrArg (fun f : AddMonoid.End A => f d) (bezout g)
  change H g (R d) + (-2*g^2-g+4 : AddMonoid.End A) (K g d) = (10 : ℕ) • d at hb
  rw [hkd, map_zero, add_zero, hd] at hb
  exact hb

/-- Every affine E667 magma on an abelian group of order coprime to ten
has an idempotent. The linear coefficients need not be assumed to commute. -/
theorem affine_has_idempotent (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) (hn : (Nat.card A).Coprime 10) :
    ∃ x, op f g c x x = x := by
  have hf := normalized f g c h
  subst f
  exact idempotent_of_coprime g c ((law_iff g c).mp h).2 hn

theorem full_law_iff (f g : AddMonoid.End A) (c : A) :
    @Equation667 A ⟨op f g c⟩ ↔ f = -(g^3) ∧ P g = 0 ∧ K g c = 0 := by
  constructor
  · intro h
    have hf := normalized f g c h
    refine ⟨hf,?_⟩
    subst f
    exact (law_iff g c).mp h
  · rintro ⟨rfl,hp,hk⟩
    exact (law_iff g c).mpr ⟨hp,hk⟩

theorem factor_P (g : AddMonoid.End A) :
    P g = (g^2+1)*(g^3-g-1)*(g^3-g+1) := by
  dsimp [P]
  noncomm_ring

theorem factor_K (g : AddMonoid.End A) : K g = -(g^2+1)*(g^3-g-1) := by
  dsimp [K]
  noncomm_ring

/-- E667 forces every affine operation over an abelian group to be medial,
even when commuting coefficients were not part of the ansatz. -/
theorem medial (f g : AddMonoid.End A) (c : A) (h : @Equation667 A ⟨op f g c⟩)
    (x y z w : A) :
    op f g c (op f g c x y) (op f g c z w) =
      op f g c (op f g c x z) (op f g c y w) := by
  have hf := normalized f g c h
  subst f
  simp only [op, end_neg_apply, pow_succ, pow_zero, end_mul_apply, end_one_apply,
    map_add, map_neg]
  abel

/-- Nonmedial E667 magmas cannot become affine over any abelian group
by an arbitrary change of labels. -/
theorem no_affine_representation {Q : Type*} [Magma Q] (hQ : Equation667 Q)
    (hn : ¬ ∀ x y z w : Q, (x ◇ y) ◇ (z ◇ w) = (x ◇ z) ◇ (y ◇ w))
    (e : Q ≃ A) (f g : AddMonoid.End A) (c : A)
    (he : ∀ x y : Q, e (x ◇ y) = op f g c (e x) (e y)) : False := by
  have hA : @Equation667 A ⟨op f g c⟩ := by
    intro x y
    obtain ⟨a,rfl⟩ := e.surjective x
    obtain ⟨b,rfl⟩ := e.surjective y
    have hh := congrArg e (hQ a b)
    simpa only [he] using hh
  apply hn
  intro x y z w
  apply e.injective
  simpa only [he] using medial f g c hA (e x) (e y) (e z) (e w)

spectrum_assert medial complete
spectrum_assert no_affine_representation complete
spectrum_assert full_law_iff complete
spectrum_assert affine_has_idempotent complete
spectrum_assert law_iff complete
spectrum_assert bezout complete
end Spectrum.E667.AffineStructure
