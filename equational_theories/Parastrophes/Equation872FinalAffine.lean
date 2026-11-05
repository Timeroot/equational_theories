import equational_theories.Parastrophes.Equation872FinalCandidate

/-!
# The final E872 candidate works for every commutative-ring affine operation

There are no exceptional characteristics or assumptions of reducedness.
Polynomial combination certificates force the two image-basis laws and an
explicit inverse for the right coefficient, on finite or infinite rings.
This is a restricted characterization, not an unrestricted catalogue result.
-/
namespace Parastrophes.Eq872FinalAffine
open Law FreeMagma AffineIdentityCertificate Eq872FinalCandidate
variable {R : Type} [CommRing R]

private def fx (p q : R) : R := p^5*q^7 + 2*p^4*q^8 + p^4*q^6 + p^3*q^9 + p^3*q^8 + p^3*q^7 + p^3*q^5 + p^3*q^2 + p^2*q^9 + p^2*q^8 + p^2*q^7 + p^2*q^6 + p^2*q^4 + p^2*q^3 + p*q^9 + q^3 - 1

private def fy (p q : R) : R := p^2*q^2 + p^2

private def fz (p q : R) : R := p^4*q^4 + p^4*q + p^3*q^5 + p^3*q^3 + p^3*q^2 + p^2*q^5 + p*q^2 + p*q

private def fc (p q : R) : R := p^4*q^7 + p^3*q^8 + p^3*q^7 + p^3*q^6 + p^3*q^4 + p^3*q + p^2*q^8 + p^2*q^7 + p^2*q^6 + p^2*q^5 + p^2*q^4 + p^2*q^3 + p^2*q^2 + p^2*q + p*q^8 + p*q^7 + p*q^6 + p*q^5 + p*q^4 + p*q^3 + p*q^2 + p*q + p + q^2 + q + 1

private theorem coefficient_formula (p q s : R) :
    coefficients p q s (Eq872GaussianAffine.candidates26[0]) =
      ⟨fx p q+1, fy p q, fz p q, s*fc p q⟩ := by
  apply Coefficients.ext <;>
    simp [Eq872GaussianAffine.candidates26, coefficients, fx, fy, fz, fc] <;> ring

/-- The variable coefficients force two small polynomial identities. The
certificates have integer coefficients, so no characteristic is excluded. -/
private theorem constraints (p q s : R) (h : Candidate (affine p q s)) :
    p^2-p-q^3+1=0 ∧ p*(q^2+1)=0 ∧ s*fc p q=0 := by
  have hc := coefficients_of_satisfies p q s (Eq872GaussianAffine.candidates26[0])
    ((models_iff (affine p q s)).mpr h)
  rw [coefficient_formula] at hc
  have hx : fx p q=0 := by
    have he := congrArg Coefficients.x hc
    dsimp at he
    linear_combination he
  have hy : fy p q=0 := congrArg Coefficients.y hc
  have hz : fz p q=0 := congrArg Coefficients.z hc
  have hs : s*fc p q=0 := congrArg Coefficients.constant hc
  dsimp [fx, fy, fz] at hx hy hz
  refine ⟨?_, ?_, hs⟩
  · linear_combination (-p^2*q^3 + 2*p^2*q^2 + 9*p^2 - p*q^3 - p*q^2 + p - 1)*hx + (2*p^5*q^4 + 4*p^5*q^3 + 4*p^5*q^2 - 4*p^5*q + 2*p^4*q^5 + 4*p^4*q^4 + 9*p^4*q^3 - 9*p^4*q^2 - 9*p^4*q - 2*p^3*q^5 + 8*p^3*q^4 - 15*p^3*q^3 - 14*p^3*q^2 + p^3*q - 3*p^2*q^7 - 12*p^2*q^6 - 4*p^2*q^5 + 4*p^2*q^4 + 5*p^2*q^3 + p^2*q^2 - 4*p^2*q - 8*p*q^7 + 9*p*q^5 + 14*p*q^4 + 4*p*q^3 - 13*p*q^2 - 9*p*q + 2*q^9 - q^8 - 3*q^7 - q^6 + 4*q^5 + 4*q^4 - 6*q^3 - 3*q^2 + q + 10)*hy + (p^3*q^6 - 2*p^3*q^5 - 10*p^3*q^3 - 4*p^3*q + 4*p^3 + p^2*q^7 - p^2*q^6 + p^2*q^5 - 10*p^2*q^4 + 5*p^2*q + 9*p^2 + p*q^7 + p*q^6 - 4*p*q - p + q^7 - q^6 + q^5 + q^3 - q^2 - q)*hz
  · linear_combination (p^3*q - p^3 + p^2*q - 2*p^2 - p)*hx + (-p^6*q^2 - 3*p^5*q^3 - 2*p^5*q^2 + p^5*q - 3*p^4*q^4 - 4*p^4*q^3 + p^4*q^2 + 2*p^4*q - 3*p^3*q^4 + p^3*q^2 + 2*p^2*q^6 + 3*p^2*q^5 - 3*p^2*q^4 - 4*p^2*q^3 - p^2*q^2 + p^2*q + 2*p*q^7 + p*q^6 - 4*p*q^4 - 3*p*q^3 + 2*p*q^2 + 3*p*q - p + q^7 - q^4 - q^3 + q - 2)*hy + (-p^4*q^4 + p^4*q^3 + p^4*q - p^3*q^5 + 2*p^3*q^3 + p^3*q^2 + 2*p^3*q - p^3 - p^2*q^5 + 2*p^2*q^4 + p^2*q^3 + p^2*q - 2*p^2 - p*q^5 + p*q^4 + 2*p*q + q)*hz

/-- Every affine model of the candidate is an actual left-division image.
The source multiplication is also affine, with an explicit polynomial inverse. -/
theorem image_of_candidate (p q s : R) (h : Candidate (affine p q s)) :
    InImage Law872 .left (affine p q s) := by
  obtain ⟨hH,hB,hs⟩ := constraints p q s h
  have hG : q^5+q^3-q^2-1=0 := by
    linear_combination -(q^2+1)*hH+(p-1)*hB
  have hu : s*(p*q^2+q^2+q+1)=0 := by
    dsimp [fc] at hs
    linear_combination hs + s*((-p^2*q^7 - p*q^8 - 2*p*q^7 - p*q^6 - p*q^4 - p*q - q^10 - 2*q^8 - 2*q^7 - 2*q^6 - q^5 - 2*q^4 - q^3 - q^2 - 2*q)*hH + (-q^9 - 3*q^8 + q^6 - 2*q^5 - 3*q^4 - 2*q - 1)*hB + (-q^8 - q^6 - 2*q^5 - q^4 + q^3 - q^2 - 2*q)*hG)
  have hv : s*(p*q*(p*q+q+1)+q^2+q+1)=0 := by
    linear_combination (2-q)*hu + s*((q^2)*hH + (q)*hB + (1)*hG)
  have hb : Eq872Image.Basis (affine p q s) := by
    constructor
    · intro x
      change x = (affine p q s).op x (Eq872Image.core (affine p q s) x)
      simp only [Eq872Image.core, affine_op]
      linear_combination -hu - x*((q^2)*hH + (q + 1)*hB + (1)*hG)
    · intro x y
      simp only [Eq872Image.core, affine_op]
      linear_combination -hv - x*((p*q^2 + q^3 + q^2 + q)*hH + (q^3 + q)*hB + (q + 1)*hG) - y*((1)*hB)
  let inv := q^4+q^2-q
  have hq : q*inv=1 := by dsimp [inv]; linear_combination hG
  let M : Magma R := ⟨fun x y => inv*(y-p*x-s)⟩
  have hd : IsDivision .left (affine p q s) M := by
    constructor
    · intro x y
      change p*x+q*(inv*(y-p*x-s))+s=y
      linear_combination (y-p*x-s)*hq
    · intro x y
      change inv*(p*x+q*y+s-p*x-s)=y
      linear_combination y*hq
  exact ⟨M, (@Law872.models_iff R M).mpr
    (Eq872Image.backward M _ (division_symm hd) hb), division_symm hd⟩

theorem characterizes_affine (p q s : R) :
    Candidate (affine p q s) ↔ InImage Law872 .left (affine p q s) :=
  ⟨image_of_candidate p q s, Eq872FinalCandidate.forward (affine p q s)⟩
end Parastrophes.Eq872FinalAffine
