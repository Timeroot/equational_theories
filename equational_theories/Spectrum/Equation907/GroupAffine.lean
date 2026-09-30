import equational_theories.Spectrum.Equation907.Affine
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite

/-! Even-order group-affine constructions cannot satisfy E907, including
endomorphisms of nonabelian groups and an arbitrary constant term. -/
namespace Spectrum.E907.GroupAffine
variable {G : Type*} [Group G]

def op (f g : G →* G) (c x y : G) := f x * g y * c

theorem commute_of_product (a b : MulAut G) (h : ∀ x, a x * b x = x) :
    ∀ x y : G, x * y = y * x := by
  have key (u v : G) : a v * b u = b u * a v := by
    apply mul_left_cancel (a := a u)
    apply mul_right_cancel (b := b v)
    calc
      a u * (a v * b u) * b v = a (u * v) * b (u * v) := by simp [mul_assoc]
      _ = u * v := h (u * v)
      _ = (a u * b u) * (a v * b v) := by rw [h u, h v]
      _ = a u * (b u * a v) * b v := by group
  intro x y
  simpa using key (b.symm y) (a.symm x)

theorem automorphisms_commutative (f g : MulAut G) (c : G)
    (h : @Equation907 G ⟨op f.toMonoidHom g.toMonoidHom c⟩) :
    ∀ x y : G, x * y = y * x := by
  let d := g (f c)
  let e := g (g c) * g c * c
  have he (x : G) : x = g (f (g x)) * d * g (g (f x)) * e := by
    calc
      x = op f.toMonoidHom g.toMonoidHom c 1
        (op f.toMonoidHom g.toMonoidHom c
          (op f.toMonoidHom g.toMonoidHom c 1 x)
          (op f.toMonoidHom g.toMonoidHom c x 1)) := h x 1
      _ = _ := by simp only [op, d, e, map_mul, map_one, one_mul, mul_one, MulEquiv.coe_toMonoidHom]; group
  have hde : d * e = 1 := by simpa only [map_one, one_mul, mul_one] using (he 1).symm
  have hed : e = d⁻¹ := by
    apply mul_left_cancel (a := d)
    rw [hde, mul_inv_cancel]
  let a : MulAut G := (g.trans f).trans g
  let b : MulAut G := ((f.trans g).trans g).trans (MulAut.conj d)
  apply commute_of_product a b
  intro x
  change g (f (g x)) * (d * g (g (f x)) * d⁻¹) = x
  rw [← hed]
  simpa only [mul_assoc] using (he x).symm


/-- In a finite group-affine model, both coefficient homomorphisms are automorphisms. -/
theorem coefficients_bijective [Finite G] (f g : G →* G) (c : G)
    (h : @Equation907 G ⟨op f g c⟩) : Function.Bijective f ∧ Function.Bijective g := by
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x,hx⟩ := @E907.left_surjective G ⟨op f g c⟩ h 1 (z * c)
    refine ⟨x, ?_⟩
    apply mul_right_cancel (b := c)
    simpa only [op, map_one, one_mul] using hx
  have hgi : Function.Injective g := Finite.injective_iff_surjective.mpr hg
  let d := g (f c)
  let e := g (g c) * g c * c
  have he (y : G) : 1 = f y * g (f (f y)) * d * g (g (g y)) * e := by
    calc
      1 = op f g c y (op f g c (op f g c y 1) (op f g c 1 y)) := h 1 y
      _ = _ := by simp only [op, d, e, map_mul, map_one, one_mul, mul_one]; group
  have hde : d * e = 1 := by simpa only [map_one, one_mul, mul_one] using (he 1).symm
  have hker (y : G) (hy : f y = 1) : y = 1 := by
    have hh : d * g (g (g y)) * e = d * 1 * e := by
      calc
        d * g (g (g y)) * e = 1 := by simpa only [hy, map_one, one_mul] using (he y).symm
        _ = d * 1 * e := by rw [mul_one, hde]
    have hggg := mul_left_cancel (mul_right_cancel hh)
    apply hgi; apply hgi; apply hgi
    simpa only [map_one] using hggg
  have hf : Function.Injective f := by
    intro x y hxy
    apply mul_inv_eq_one.mp
    apply hker
    simp only [map_mul, map_inv, hxy, mul_inv_cancel]
  exact ⟨⟨hf,Finite.injective_iff_surjective.mp hf⟩,⟨hgi,hg⟩⟩

/-- The group underlying any finite group-affine E907 model is commutative. -/
theorem commutative [Finite G] (f g : G →* G) (c : G)
    (h : @Equation907 G ⟨op f g c⟩) : ∀ x y : G, x * y = y * x := by
  obtain ⟨hf,hg⟩ := coefficients_bijective f g c h
  exact automorphisms_commutative (MulEquiv.ofBijective f hf) (MulEquiv.ofBijective g hg) c h

/-- No even-order E907 model arises from endomorphisms of a group. -/
theorem odd_card [Fintype G] (f g : G →* G) (c : G)
    (h : @Equation907 G ⟨op f g c⟩) : Odd (Fintype.card G) := by
  letI : CommGroup G := { ‹Group G› with mul_comm := commutative f g c h }
  let A : AddMonoid.End (Additive G) := f.toAdditive
  let B : AddMonoid.End (Additive G) := g.toAdditive
  have hh : @Equation907 (Additive G) ⟨Affine.op A B (Additive.ofMul c)⟩ := h
  simpa only [Fintype.card_additive] using Affine.odd_card A B (Additive.ofMul c) hh

spectrum_assert coefficients_bijective complete
spectrum_assert commutative complete
spectrum_assert odd_card complete

/-- info: 'Spectrum.E907.GroupAffine.odd_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_card
end Spectrum.E907.GroupAffine
