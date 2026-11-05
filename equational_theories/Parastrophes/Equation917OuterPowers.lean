import equational_theories.Parastrophes.Equation917SandwichCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# No number of outer unit iterations repairs the E917 crossed identity

Put `q(x)=(x*(x*x))*x`, `U(x)=x*q(x)`, and `H(x,y)=q(x)*(x*y)`.
Every finite E917 left-division image satisfies

    U^[k](y) * H(x,y) = x

for every natural k. However, NONE of these single identities characterizes
the image. Six small affine quasigroups cover all exponents, by their residue
modulo twelve. Their orders are 13, 13, 29, 37, 157, and 197.

Only scalar coefficients are checked. There are no multiplication tables,
SAT certificates, native decisions, or enumerations of pairs of elements.
This eliminates an infinite family of proposals, not every possible single
identity: the unrestricted catalogue question remains open.
-/
namespace Parastrophes.Eq917Image.OuterPowers
open Law
open SandwichCandidate (U H)

def Identity {A : Type} (D : Magma A) (k : ℕ) : Prop :=
  ∀ x y, D.op ((U D)^[k] y) (H D x y) = x

theorem of_image {A : Type} [Finite A] (D : Magma A)
    (h : InImage Law917 .left D) (k : ℕ) : Identity D k := by
  have hb := (characterizes_fin D).mpr h
  intro x y
  have hu : U D y = y := (hb.1 y).symm
  rw [Function.iterate_fixed hu k]
  exact (hb.2 x y).symm

section Ring
variable {R : Type} [CommRing R]

@[implicit_reducible] def affine (a b : R) : Magma R := ⟨fun x y => a*x+b*y⟩

def qCoeff (a b : R) : R := a^2+a^2*b+a*b^2+b
def uCoeff (a b : R) : R := a+b*qCoeff a b

theorem core_affine (a b x : R) : core (affine a b) x = qCoeff a b*x := by
  dsimp [core, affine, qCoeff]
  ring

theorem unit_affine (a b x : R) : U (affine a b) x = uCoeff a b*x := by
  dsimp only [U]
  rw [core_affine]
  change a*x+b*(qCoeff a b*x) = _
  dsimp [uCoeff]
  ring

theorem iterate_affine (a b x : R) (k : ℕ) :
    (U (affine a b))^[k] x = uCoeff a b^k*x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', unit_affine, ih, pow_succ]; ring

theorem identity_of_coefficients (a b : R) (k : ℕ)
    (hx : a*b*(qCoeff a b+b)=1)
    (hy : a*uCoeff a b^k+b^3=0) : Identity (affine a b) k := by
  intro x y
  rw [iterate_affine]
  dsimp only [H]
  rw [core_affine]
  change a*(uCoeff a b^k*y)+b*(a*(qCoeff a b*x)+b*(a*x+b*y))=x
  linear_combination x*hx+y*hy

theorem not_image (a b : R) (hu : uCoeff a b ≠ 1) :
    ¬ InImage Law917 .left (affine a b) := by
  rintro ⟨M, hm, hd⟩
  have h := (forward M _ hd ((@Law917.models_iff R M).mp hm)).1 1
  have he : U (affine a b) 1 = 1 := h.symm
  rw [unit_affine, mul_one] at he
  exact hu he

theorem affine_quasigroup (a b ai bi : R) (ha : ai*a=1) (hb : bi*b=1) :
    IsQuasigroup (affine a b) := by
  constructor
  · intro x
    constructor
    · intro y z he
      change a*x+b*y=a*x+b*z at he
      linear_combination bi*he-(y-z)*hb
    · intro y
      refine ⟨bi*(y-a*x), ?_⟩
      change a*x+b*(bi*(y-a*x))=y
      linear_combination (y-a*x)*hb
  · intro y
    constructor
    · intro x z he
      change a*x+b*y=a*z+b*y at he
      linear_combination ai*he-(x-z)*ha
    · intro x
      refine ⟨ai*(x-b*y), ?_⟩
      change a*(ai*(x-b*y))+b*y=x
      linear_combination (x-b*y)*ha
end Ring

private def seed (r : Fin 12) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  if r.val % 4 = 0 then (29,18,15,21,2)
  else if r.val % 4 = 1 then (197,25,166,134,108)
  else if r.val % 4 = 3 then (37,14,33,8,9)
  else if r.val = 2 then (157,154,89,52,30)
  else if r.val = 6 then (13,12,10,12,4)
  else (13,4,4,10,10)

/-- The entire finite certificate: twelve selections from six five-number seeds. -/
private theorem seed_checks : ∀ r : Fin 12,
    let (p,a,b,ai,bi) := seed r
    let A : ZMod p := a
    let B : ZMod p := b
    0 < p ∧ p ≤ 197 ∧
    (ai : ZMod p)*A=1 ∧ (bi : ZMod p)*B=1 ∧
    A*B*(qCoeff A B+B)=1 ∧ uCoeff A B^12=1 ∧
    A*uCoeff A B^r.val+B^3=0 ∧ uCoeff A B ≠ 1 := by
  decide +kernel

/-- Every proposed exponent has a quasigroup counterexample of order at most
197. The reduction modulo twelve is mathematical, not a bounded exponent check. -/
theorem counterexample (k : ℕ) :
    ∃ (p : ℕ) (D : Magma (ZMod p)), 0 < p ∧ p ≤ 197 ∧
      IsQuasigroup D ∧ Identity D k ∧ ¬ InImage Law917 .left D := by
  let r : Fin 12 := ⟨k % 12, Nat.mod_lt _ (by decide)⟩
  rcases hs : seed r with ⟨p,a,b,ai,bi⟩
  have hc := seed_checks r
  rw [hs] at hc
  dsimp only at hc
  obtain ⟨hp,hbound,ha,hb,hx,ht,hy,hu⟩ := hc
  let A : ZMod p := a
  let B : ZMod p := b
  have power : uCoeff A B^k = uCoeff A B^(k % 12) := by
    conv_lhs => rw [← Nat.mod_add_div k 12]
    rw [pow_add, pow_mul, ht, one_pow, mul_one]
  refine ⟨p,affine A B,hp,hbound,affine_quasigroup A B ai bi ha hb,?_,not_image A B hu⟩
  apply identity_of_coefficients A B k hx
  rw [power]
  exact hy

theorem no_characterization (k : ℕ) :
    ¬ (∀ (A : Type) [Finite A] (D : Magma A),
      Identity D k ↔ InImage Law917 .left D) := by
  intro h
  obtain ⟨p,D,hp,_,_,hi,hn⟩ := counterexample k
  letI : NeZero p := ⟨by omega⟩
  exact hn ((h (ZMod p) D).mp hi)

end Parastrophes.Eq917Image.OuterPowers
