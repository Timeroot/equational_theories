import equational_theories.Parastrophes.Equation917CompositionCandidate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The E917 composition candidate has no finite scalar-affine counterexample

This proves the restricted converse for every finite commutative coefficient
ring, including nonfields and rings with nilpotents. It is not the unrestricted
single-equation characterization. The key Bezout identity has integer
coefficients and constant 1, so there are no exceptional characteristics.
-/
namespace Parastrophes.Eq917Image.CompositionCandidate.Affine
open SandwichCandidate (F G H U)

variable {R : Type} [CommRing R] [Finite R]

@[implicit_reducible] def magma (a b d : R) : Magma R := ⟨fun x y => a*x+b*y+d⟩

private def P (b : R) := b^11+b^10-b^9+2*b^5+1
private def Q (b : R) := b^8+b^7-b^6-b^3+b^2-1
private def T (b : R) := b^8+b^7-b^4+b^2+b+1
private def V (b : R) := 1+b-b^4-b^5
private def C (b : R) := (b+1)*(b^2+1)

theorem basis (a b d : R) (h : Identity (magma a b d)) : Basis (magma a b d) := by
  let D := magma a b d
  change Identity D at h
  obtain ⟨f, g, _, _, hf, hg, hc⟩ := common_maps D h 0
  have hq := (quasigroup D h).1
  have cancel_b (z : R) (hz : b*z = 0) : z = 0 := by
    apply (hq 0).1
    change a*0+b*z+d = a*0+b*0+d
    simp only [hz, mul_zero]
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
  have he (x : R) : U D x + 4*v + 2*T b*d = x := by
    have hh := h x 0 0 0 0 0 0
    rw [hF, hF, hG, hG, hG, hG] at hh
    linear_combination hh
  have hz := he 0
  have ho := he 1
  rw [hU] at hz ho
  have hpoly : Q b = 0 := by linear_combination ho - hz
  have hoff : ((2*b+4)*T b+b*V b)*d = 0 := by
    linear_combination b*hz - 4*hv
  have hk : C b*(b^3-b+1) = 0 := by
    dsimp [C, P, Q] at *
    linear_combination hp - b^3*hpoly
  have hcd : C b*d = 0 := by
    dsimp [C, T, V] at *
    linear_combination
      (24*b^5+16*b^4-46*b^3+37)*d*hk + (-12*b^2+16*b-9)*hoff
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
    Identity (magma a b d) ↔ InImage Law917 .left (magma a b d) :=
  ⟨fun h => (characterizes_fin _).mp (basis a b d h), of_image _⟩

end Parastrophes.Eq917Image.CompositionCandidate.Affine
