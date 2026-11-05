import equational_theories.Parastrophes.Equation917PowerComparison
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-!
# Noncommuting additive coefficients in the E917 candidate

For `x*y=a(x)+b(y)+k`, the forty-operation candidate forces `a=-b³`.
Here a and b are arbitrary additive endomorphisms of any abelian group;
commutation, invertibility and finiteness are not assumed. Comparing the
outer parameter v with zero gives `a(b(v))+b⁴(v)=0`. Surjective rows make
b surjective, giving the asserted formula. It immediately implies that the
two coefficients commute. The candidate also forces b injective.

This eliminates noncommuting matrices as counterexamples to the candidate.
It does not assert that arbitrary candidate magmas admit an affine form.
-/
namespace Parastrophes.Eq917Image.PowerComparison.Additive
open SandwichCandidate (U H)

variable {G : Type} [AddCommGroup G]

@[implicit_reducible] def affine (a b : G →+ G) (k : G) : Magma G :=
  ⟨fun x y => a x + b y + k⟩

theorem right_surjective (a b : G →+ G) (k : G)
    (h : Identity (affine a b k)) : Function.Surjective b := by
  intro y
  obtain ⟨x, hx⟩ := rows_surjective (affine a b k) h 0 (y+k)
  change a 0 + b x + k = y+k at hx
  simp only [map_zero, zero_add] at hx
  exact ⟨x, add_right_cancel hx⟩

theorem coefficients (a b : G →+ G) (k : G)
    (h : Identity (affine a b k)) : ∀ x, a x = -b (b (b x)) := by
  let D := affine a b k
  have difference (s t v : G) :
      D.op (D.op s v) (H D 0 (D.op t v)) =
        D.op (D.op s 0) (H D 0 (D.op t 0)) + a (b v) + b (b (b (b v))) := by
    change a (a s+b v+k) +
      b (a (core D 0)+b (a 0+b (a t+b v+k)+k)+k)+k =
        (a (a s+b 0+k) +
          b (a (core D 0)+b (a 0+b (a t+b 0+k)+k)+k)+k) +
            a (b v)+b (b (b (b v)))
    simp only [map_add, map_zero, zero_add, add_zero]
    abel
  have relation (v : G) : a (b v) + b (b (b (b v))) = 0 := by
    let s := D.op (U D (U D 0)) (D.op (U D 0) 0)
    let t := D.op 0 (D.op 0 0)
    have he := (h 0 0 0 0 v).symm.trans (h 0 0 0 0 0)
    change D.op (D.op s v) (H D 0 (D.op t v)) =
      D.op (D.op s 0) (H D 0 (D.op t 0)) at he
    rw [difference, add_assoc] at he
    exact add_left_cancel (he.trans (add_zero _).symm)
  intro x
  obtain ⟨v, rfl⟩ := right_surjective a b k h x
  exact eq_neg_of_add_eq_zero_left (relation v)

theorem coefficients_commute (a b : G →+ G) (k : G)
    (h : Identity (affine a b k)) : Function.Commute a b := by
  intro x
  rw [coefficients a b k h, coefficients a b k h, map_neg]

/-- This also works on infinite abelian groups. A collision of b gives a
collision of a, hence of the entire right side of the candidate. -/
theorem right_bijective (a b : G →+ G) (k : G)
    (h : Identity (affine a b k)) : Function.Bijective b := by
  refine ⟨?_, right_surjective a b k h⟩
  intro x y he
  have ha : a x = a y := by rw [coefficients a b k h, coefficients a b k h, he]
  let D := affine a b k
  have hl (z : G) : D.op x z = D.op y z := by change a x+b z+k = a y+b z+k; rw [ha]
  have hr (z : G) : D.op z x = D.op z y := by change a z+b x+k = a z+b y+k; rw [he]
  have hq : core D x = core D y := by
    unfold core
    rw [hl, hr, hl, hr]
  have hh (z : G) : H D x z = H D y z := by simp only [H, hq, hl]
  exact (h x 0 0 0 0).trans
    ((congrArg (D.op (D.op (D.op (U D (U D 0)) (D.op (U D 0) 0)) 0)) (hh _)).trans
      (h y 0 0 0 0).symm)

theorem coefficients_bijective (a b : G →+ G) (k : G)
    (h : Identity (affine a b k)) : Function.Bijective a ∧ Function.Bijective b := by
  have hb := right_bijective a b k h
  have hn : Function.Bijective (fun x : G => -x) :=
    ⟨neg_injective, fun x => ⟨-x, neg_neg x⟩⟩
  refine ⟨?_, hb⟩
  have he : (a : G → G) = (fun x : G => -x) ∘ b ∘ b ∘ b := by
    funext x
    exact coefficients a b k h x
  rw [he]
  exact ((hn.comp hb).comp hb).comp hb

end Parastrophes.Eq917Image.PowerComparison.Additive
