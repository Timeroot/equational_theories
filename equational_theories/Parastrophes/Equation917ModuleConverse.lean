import equational_theories.Parastrophes.Equation917AdditiveCoefficients
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Module.Hom

/-!
# The E917 candidate on modules

The coefficient argument reduces an arbitrary additive isotope to
`x*y = -b³(x)+b(y)+d`. The calculation below works on modules, where
polynomials in b annihilate vectors; it does not assume a faithful scalar
representation or a field. The integral Bezout identity has constant one,
so no characteristic or torsion case is omitted.
-/
namespace Parastrophes.Eq917Image.PowerComparison.ModuleConverse
open SandwichCandidate (U H F)

variable {R G : Type} [CommRing R] [AddCommGroup G] [Module R G]

@[implicit_reducible] def magma (b : R) (d : G) : Magma G :=
  ⟨fun x y => -(b^3) • x + b • y + d⟩

private def P (b : R) := b^11+b^10-b^9+2*b^5+1
private def Q (b : R) := b^8+b^7-b^6-b^3+b^2-1
private def C (b : R) := (b+1)*(b^2+1)
private def W (b : R) := b^12+2*b^11-b^10-2*b^9+b^5-b^3+1

theorem basis (b : R) (d : G) (hi : Function.Injective (fun x : G => b • x))
    (h : Identity (magma b d)) : Basis (magma b d) := by
  let D := magma b d
  have hp (x : G) : P b • x = 0 := by
    have he := h x 0 0 0 0
    have hz := h 0 0 0 0 0
    dsimp [magma, Magma.op, U, core, H] at he hz
    dsimp [P]
    linear_combination (norm := module) he - hz
  have hq (x : G) : Q b • x = 0 := by
    have he := (h 0 0 x 0 0).symm.trans (h 0 0 0 0 0)
    dsimp [magma, Magma.op, U, core, H] at he
    have hh : b^10 • (Q b • x) = 0 := by
      dsimp [Q]
      linear_combination (norm := module) -he
    have hi10 : Function.Injective (fun z : G => b^10 • z) := by
      have hip (n : ℕ) : Function.Injective (fun z : G => b^n • z) := by
        induction n with
        | zero => simpa only [pow_zero, one_smul] using (Function.injective_id : Function.Injective (id : G → G))
        | succ n ih => simpa only [pow_succ', mul_smul] using hi.comp ih
      exact hip 10
    exact hi10 (hh.trans (smul_zero _).symm)
  have hoff : (C b*W b) • d = 0 := by
    have he := h 0 0 0 0 0
    have hqd := hq d
    dsimp [magma, Magma.op, U, core, H] at he
    dsimp [C, W, Q] at *
    linear_combination (norm := module) -he - (b^14+b^13-b^10-b^9) • hqd
  have hk (x : G) : (C b*(b^3-b+1)) • x = 0 := by
    have hpx := hp x
    have hqx := hq x
    dsimp [C, P, Q] at *
    linear_combination (norm := module) hpx - b^3 • hqx
  have hcd : C b • d = 0 := by
    have hkd := hk d
    dsimp [C, W] at *
    linear_combination (norm := module)
      (-2*b^11-6*b^10-3*b^9+4*b^8+6*b^7+5*b^6+2*b^5-3*b^4-5*b^3-2*b^2+2) • hkd +
        (2*b^2+2*b-1) • hoff
  have hu (x : G) : U D x = x := by
    have hqx := hq x
    dsimp [U, core, D, magma, Q, C] at *
    linear_combination (norm := module) hqx - ((b-1)*(b+1)) • hcd
  have hf (x y : G) : F D x y = x := by
    have hpx := hp x
    dsimp [F, H, core, D, magma, P, C] at *
    linear_combination (norm := module) -hpx + (b^5-b^3+1) • hcd
  exact ⟨fun x => (hu x).symm, fun x y => (hf x y).symm⟩

end Parastrophes.Eq917Image.PowerComparison.ModuleConverse

namespace Parastrophes.Eq917Image.PowerComparison.Additive
open Polynomial
open SandwichCandidate (U H)

variable {G : Type} [AddCommGroup G]

/-- The full candidate converse for arbitrary additive endomorphisms, including
noncommuting input coefficients, mixed torsion and infinite abelian groups.
The polynomial variable acts as b; the coefficient theorem forces a=-b³. -/
theorem basis (a b : G →+ G) (k : G) (h : Identity (affine a b k)) :
    Basis (affine a b k) := by
  let rho : ℤ[X] →+* AddMonoid.End G :=
    Polynomial.eval₂RingHom' (S := AddMonoid.End G) (Int.castRingHom _) b
      (fun z => @Int.cast_commute (AddMonoid.End G) _ z b)
  letI : Module ℤ[X] G := Module.compHom G rho
  have hb (x : G) : (X : ℤ[X]) • x = b x := by
    change rho X x = b x
    simp [rho]
    rfl
  have ha (x : G) : -(X^3 : ℤ[X]) • x = a x := by
    rw [coefficients a b k h]
    simp only [neg_smul, pow_succ, pow_zero, mul_smul, one_smul, hb]
  have hm : ModuleConverse.magma (X : ℤ[X]) k = affine a b k := by
    unfold ModuleConverse.magma affine
    congr 1
    funext x y
    exact congrArg (fun z => z + k) (congrArg₂ (· + ·) (ha x) (hb y))
  have hi : Function.Injective (fun x : G => (X : ℤ[X]) • x) := by
    simpa only [hb] using (right_bijective a b k h).1
  rw [← hm] at h ⊢
  exact ModuleConverse.basis _ _ hi h

/-- An exact characterization on this whole construction family. The catalogue
row remains open because arbitrary magmas need not have an additive form. -/
theorem characterizes (a b : G →+ G) (k : G) :
    Identity (affine a b k) ↔ InImage Law917 .left (affine a b k) := by
  constructor
  · intro h
    let D := affine a b k
    have hb := basis a b k h
    have hi (x : G) : Function.Injective (D.op x) := by
      intro y z he
      apply (right_bijective a b k h).1
      change a x + b y + k = a x + b z + k at he
      exact add_left_cancel (add_right_cancel he)
    let M : Magma G := ⟨fun x y => H D y x⟩
    have he (x y : G) : D.op x (M.op x y) = y := (hb.2 y x).symm
    have hd : IsDivision .left M D :=
      ⟨fun x y => hi x (he x (D.op x y)), he⟩
    exact ⟨M, (@Law917.models_iff G M).mpr (backward M D hd hb), hd⟩
  · rintro ⟨M, hm, hd⟩
    exact of_basis _ (forward M _ hd ((@Law917.models_iff G M).mp hm))

end Parastrophes.Eq917Image.PowerComparison.Additive
