import equational_theories.Parastrophes.Equation917PowerComparison
import equational_theories.Parastrophes.Equation917SandwichAffine

/-!
# Exact affine converse for the forty-operation E917 candidate

This theorem covers every commutative ring, not just finite fields. It does
not assert the converse for arbitrary magmas. Surjectivity of a row makes
the right coefficient a unit. The variable coefficients then give A=-B³,
P(B)=Q(B)=0. The constant coefficient and an integral Bezout identity kill
both remaining translations. The Bezout constant is one; in particular no
exceptional characteristic is discarded.
-/
namespace Parastrophes.Eq917Image.PowerComparison.Affine
open SandwichCandidate (U H F)
open SandwichCandidate.Affine (magma)

variable {R : Type} [CommRing R]

private def P (b : R) := b^11+b^10-b^9+2*b^5+1
private def Q (b : R) := b^8+b^7-b^6-b^3+b^2-1
private def C (b : R) := (b+1)*(b^2+1)
private def T (b : R) := b^8+b^7-b^4+b^2+b+1
private def V (b : R) := 1+b-b^4-b^5
private def W (b : R) := b^12+2*b^11-b^10-2*b^9+b^5-b^3+1

theorem basis (a b d : R) (h : Identity (magma a b d)) :
    Basis (magma a b d) := by
  let D := magma a b d
  change Identity D at h
  obtain ⟨bi, hbi⟩ := rows_surjective D h 0 (d+1)
  have hunit : b*bi = 1 := by
    change a*0+b*bi+d = d+1 at hbi
    linear_combination hbi
  have cancel_b (z : R) (hz : b*z = 0) : z = 0 := by
    linear_combination bi*hz - z*hunit
  have hab : a = -b^3 := by
    have he := (h 0 0 0 0 1).symm.trans (h 0 0 0 0 0)
    dsimp [D, magma, Magma.op, U, core, H] at he
    have hh : b*(a+b^3) = 0 := by linear_combination he
    have hz := cancel_b _ hh
    linear_combination hz
  subst a
  have hp : P b = 0 := by
    have he := h 1 0 0 0 0
    have hz := h 0 0 0 0 0
    dsimp [D, magma, Magma.op, U, core, H] at he hz
    dsimp [P]
    linear_combination he - hz
  have hq : Q b = 0 := by
    have he := (h 0 0 1 0 0).symm.trans (h 0 0 0 0 0)
    dsimp [D, magma, Magma.op, U, core, H] at he
    have hh : b^10*Q b = 0 := by
      dsimp [Q]
      linear_combination -he
    have ht : (b*bi)^10 = 1 := by rw [hunit, one_pow]
    linear_combination bi^10*hh - Q b*ht
  have hoff : C b*W b*d = 0 := by
    have he := h 0 0 0 0 0
    dsimp [D, magma, Magma.op, U, core, H] at he
    dsimp [C, W]
    dsimp [Q] at hq
    linear_combination -he - (b^14+b^13-b^10-b^9)*d*hq
  have hk : C b*(b^3-b+1) = 0 := by
    dsimp [C, P, Q] at *
    linear_combination hp - b^3*hq
  have hcd : C b*d = 0 := by
    dsimp [C, W] at *
    linear_combination
      (-2*b^11-6*b^10-3*b^9+4*b^8+6*b^7+5*b^6+2*b^5-3*b^4-5*b^3-2*b^2+2)*d*hk +
        (2*b^2+2*b-1)*hoff
  have htd : T b*d = 0 := by
    dsimp [T, C] at *
    linear_combination (b^5-b^3+1)*hcd
  have hvd : V b*d = 0 := by
    dsimp [V, C] at *
    linear_combination -(b-1)*(b+1)*hcd
  have hu (x : R) : U D x = x := by
    dsimp [U, core, D, magma]
    dsimp [Q, V] at *
    linear_combination x*hq + hvd
  have hf (x y : R) : F D x y = x := by
    dsimp [F, H, core, D, magma]
    dsimp [P, T] at *
    linear_combination -x*hp + htd
  exact ⟨fun x => (hu x).symm, fun x y => (hf x y).symm⟩

theorem characterizes (a b d : R) :
    Identity (magma a b d) ↔ InImage Law917 .left (magma a b d) := by
  constructor
  · intro h
    have hb := basis a b d h
    have hs : SandwichCandidate.Identity (magma a b d) := by
      apply SandwichCandidate.of_basis _ hb
      intro x
      have hr := rows_surjective (magma a b d) h x
      obtain ⟨z, hz⟩ := rows_surjective (magma a b d) h 0 (d+1)
      have hunit : b*z = 1 := by
        change a*0+b*z+d = d+1 at hz
        linear_combination hz
      refine ⟨?_, hr⟩
      intro y w he
      change a*x+b*y+d = a*x+b*w+d at he
      linear_combination z*he - (y-w)*hunit
    exact (SandwichCandidate.Affine.characterizes a b d).mp hs
  · rintro ⟨M, hm, hd⟩
    exact of_basis _ (forward M _ hd ((@Law917.models_iff _ M).mp hm))

end Parastrophes.Eq917Image.PowerComparison.Affine
