import equational_theories.Parastrophes.Equation917SandwichCandidate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The E917 sandwich candidate is exact for commutative-ring affine magmas

This is a restricted converse, not a characterization of arbitrary magmas.
For x*y=A*x+B*y+d, independence of the two bridge parameters forces A=-B³.
The remaining coefficient equations are P(B)=Q(B)=0 and R(B)*d=0.
Here P-B³Q=(B+1)(B²+1)(B³-B+1). An integral Bezout identity then forces
(B+1)(B²+1)*d=0. Both unwanted translations vanish, proving the image basis.

All polynomial identities have integer coefficients: the argument works over
every commutative ring, including infinite rings and rings with nilpotents.
Surjectivity of U follows from the coefficient of x in the candidate, so no
finiteness assumption is needed even in the initial common-map reduction.
-/
namespace Parastrophes.Eq917Image.SandwichCandidate.Affine

variable {R : Type} [CommRing R]

@[implicit_reducible] def magma (a b d : R) : Magma R := ⟨fun x y => a*x+b*y+d⟩

private def P (b : R) := b^11+b^10-b^9+2*b^5+1
private def Q (b : R) := b^8+b^7-b^6-b^3+b^2-1
private def T (b : R) := b^8+b^7-b^4+b^2+b+1
private def V (b : R) := 1+b-b^4-b^5
private def C (b : R) := (b+1)*(b^2+1)

/-- The candidate's coefficient of x is S³ times the coefficient of U.
It equals 1, giving an explicit inverse for the latter coefficient. -/
theorem unit_surjective (a b d : R) (h : Identity (magma a b d)) :
    Function.Surjective (U (magma a b d)) := by
  let D := magma a b d
  let k := a^2+a^2*b+a*b^2+b
  let s := b*a*(k+b)
  let c := a+b*k
  have hu (x t : R) : U D (x+t) = U D x+c*t := by
    dsimp [U, core, D, magma, c, k]
    ring
  have hh (x t y : R) : H D (x+t) y = H D x y+a*(k+b)*t := by
    dsimp [H, core, D, magma, k]
    ring
  have hf (x t y : R) : F D (x+t) y = F D x y+s*t := by
    dsimp [F, H, core, D, magma, s, k]
    ring
  have hg (y x t : R) : G D y (x+t) = G D y x+s*t := by
    dsimp [G, H, core, D, magma, s, k]
    ring
  have hm (x y t : R) : D.op x (y+t) = D.op x y+b*t := by
    change a*x+b*(y+t)+d = a*x+b*y+d+b*t
    ring
  have he := h (0+1) 0 0 0
  change (0:R)+1 = D.op 0 (F D (H D (G D 0 (U D (0+1))) 0) 0) at he
  rw [hu, hg, hh, hf, hm] at he
  have hz := h 0 0 0 0
  change (0:R) = D.op 0 (F D (H D (G D 0 (U D 0)) 0) 0) at hz
  have hi : s^3*c = 1 := by
    dsimp [s] at *
    linear_combination -he+hz
  intro t
  refine ⟨s^3*(t-U D 0), ?_⟩
  have hu' (x : R) : U D x = U D 0+c*x := by simpa using hu 0 x
  rw [hu']
  linear_combination (t-U D 0)*hi

/-- The two Bezout identities have integral coefficients, so there are no
exceptional characteristics or cancellability assumptions hidden here. -/
private theorem kill_offset (b d : R) (hp : P b = 0) (hq : Q b = 0)
    (hr : (b * V b + (b^2+b+1)*T b)*d = 0) : C b*d = 0 := by
  have hk : C b*(b^3-b+1) = 0 := by
    dsimp [C, P, Q] at *
    linear_combination hp - b^3*hq
  dsimp [C, V, T] at *
  linear_combination
    (3*b^6-b^5+b^4-5*b^3+3*b+3)*d*hk + (-3*b^2+4*b-2)*hr

theorem basis (a b d : R) (h : Identity (magma a b d)) :
    Basis (magma a b d) := by
  let D := magma a b d
  change Identity D at h
  have hus := unit_surjective a b d h
  have hq := rows_of_unit_surjective D h hus
  have cancel_b (z : R) (hz : b*z = 0) : z = 0 := by
    apply (hq 0).1
    change a*0+b*z+d = a*0+b*0+d
    simp only [hz, mul_zero]
  obtain ⟨f, g, _, _, hf, hg, hc⟩ := common_maps_of_unit_surjective D h hus
  have hab : a = -b^3 := by
    have he := (hf 0 1).trans (hf 0 0).symm
    dsimp [D, magma, F, H, core] at he
    linear_combination he
  subst a
  have hp : P b = 0 := by
    have he := (hg 1 0).trans (hg 0 0).symm
    dsimp [D, magma, G, H, core] at he
    apply cancel_b
    apply cancel_b
    dsimp [P]
    linear_combination he
  have hF (x y : R) : F D x y = x+T b*d := by
    dsimp [F, H, core, D, magma, T]
    dsimp [P] at hp
    linear_combination -x*hp
  let v := G D 0 0
  have hG (y x : R) : G D y x = x+v := by
    dsimp [v, G, H, core, D, magma]
    dsimp [P] at hp
    linear_combination (b^2*y-x)*hp
  have hv : b*v = T b*d := by
    have he := hF (D.op 0 0) 0
    change D.op 0 (G D 0 0) = D.op 0 0 + T b*d at he
    change (-b^3)*0+b*v+d = (-b^3)*0+b*0+d+T b*d at he
    linear_combination he
  have hU (x : R) : U D x = (Q b+1)*x+V b*d := by
    dsimp [U, core, D, magma, Q, V]
    ring
  have he (x : R) : x = U D x+v+(1+b)*T b*d := by
    have hh := h x 0 0 0
    rw [hF, hG] at hh
    have ht : D.op 0 (H D (U D x+v) 0 + T b*d) =
        F D (U D x+v) 0 + b*T b*d := by
      change (-b^3)*0+b*(H D (U D x+v) 0+T b*d)+d =
        (-b^3)*0+b*H D (U D x+v) 0+d+b*T b*d
      ring
    rw [ht, hF] at hh
    linear_combination hh
  have hzero := he 0
  have hone := he 1
  rw [hU] at hzero hone
  have hpoly : Q b = 0 := by linear_combination hzero - hone
  have hoff : (b*V b+(b^2+b+1)*T b)*d = 0 := by
    linear_combination -b*hzero - hv
  have hcd := kill_offset b d hp hpoly hoff
  have ht : T b*d = 0 := by
    dsimp [T, C] at *
    linear_combination (b^5-b^3+1)*hcd
  have hvd : V b*d = 0 := by
    dsimp [V, C] at *
    linear_combination -(b-1)*(b+1)*hcd
  constructor
  · intro x
    change x = U D x
    rw [hU, hpoly, hvd]
    ring
  · intro x y
    change x = F D x y
    rw [hF, ht, add_zero]

theorem characterizes (a b d : R) :
    Identity (magma a b d) ↔ InImage Law917 .left (magma a b d) := by
  refine ⟨fun h => ?_, of_image _⟩
  let D := magma a b d
  have hb := basis a b d h
  have hq := rows_of_unit_surjective D h (unit_surjective a b d h)
  let M : Magma R := ⟨fun x y => D.op (core D y) (D.op y x)⟩
  have he (x y : R) : D.op x (M.op x y) = y := (hb.2 y x).symm
  have hd : IsDivision .left M D :=
    ⟨fun x y => (hq x).1 (he x (D.op x y)), he⟩
  exact ⟨M, (@Law917.models_iff R M).mpr (backward M D hd hb), hd⟩

end Parastrophes.Eq917Image.SandwichCandidate.Affine
