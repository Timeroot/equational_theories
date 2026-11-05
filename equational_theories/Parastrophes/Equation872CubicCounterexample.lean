import equational_theories.Parastrophes.Equation872GaussianAffine
import equational_theories.Parastrophes.LinearIdentityCertificate
import Mathlib.Data.ZMod.Basic

/-!
# A 27-element counterexample to the last 28-operation image candidates

Over F27 = F3[q]/(q³+q²+q-1), use D(x,y)=(q²-1)x+qy.
The coordinate matrices below represent multiplication by q²-1 and q on
(1,q,q²). Both are invertible. Checking nine basis assignments proves each
candidate identity, while a single assignment refutes the exact image basis.
No field construction or exhaustive enumeration of triples is needed.
-/
namespace Parastrophes.Eq872CubicCounterexample
open Law FreeMagma AffineIdentityCertificate
abbrev V := Fin 3 → ZMod 3

private def coordinate (i : Fin 3) : V →ₗ[ZMod 3] ZMod 3 := LinearMap.proj i

def A : V →ₗ[ZMod 3] V := LinearMap.pi
  ![coordinate 1-coordinate 2-coordinate 0,
    2 • coordinate 2-2 • coordinate 1, coordinate 0-coordinate 1-coordinate 2]

def B : V →ₗ[ZMod 3] V := LinearMap.pi
  ![coordinate 2, coordinate 0-coordinate 2, coordinate 1-coordinate 2]

@[implicit_reducible] def magma : Magma V := LinearIdentityCertificate.magma A B

theorem basis_checks : ∀ t ∈ Eq872GaussianAffine.candidates28, ∀ i j,
    @evalInMagma _ V magma (Pi.single i (Pi.single j 1)) t =
      (Pi.single i (Pi.single j 1) : Fin 3 → V) 0 := by decide

theorem satisfies_candidate (t : FreeMagma (Fin 3)) (ht : t ∈ Eq872GaussianAffine.candidates28) :
    @satisfies _ V magma (identity t) :=
  LinearIdentityCertificate.satisfies_of_basis A B t (basis_checks t ht)

theorem not_image : ¬ InImage Law872 .left magma := by
  rintro ⟨M, hM, hd⟩
  have h := (Eq872Image.forward M magma hd ((@Law872.models_iff _ M).mp hM)).2
    0 ![0,0,1]
  exact (by decide : (0 : V) ≠ magma.op ![0,0,1]
    (magma.op (Eq872Image.core magma 0) (magma.op ![0,0,1] 0))) h

theorem refutes (t : FreeMagma (Fin 3)) (ht : t ∈ Eq872GaussianAffine.candidates28) :
    ¬ Characterizes .fin Law872 .left (identity t) := by
  intro h
  exact not_image ((h V magma (inferInstance : Finite V)).mp (satisfies_candidate t ht))

theorem quasigroup : IsQuasigroup magma := by
  have hA : Function.Injective A := Function.LeftInverse.injective
    (show Function.LeftInverse (fun v : V => ![2*v 0+v 1,v 0+v 1+v 2,v 0+v 2]) A by decide)
  have hB : Function.Injective B := Function.LeftInverse.injective
    (show Function.LeftInverse (fun v : V => ![v 0+v 1,v 0+v 2,v 0]) B by decide)
  constructor
  · intro x
    have hi : Function.Injective (magma.op x) := fun a b h => hB (add_left_cancel h)
    exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩
  · intro y
    have hi : Function.Injective (fun x => magma.op x y) := fun a b h => hA (add_right_cancel h)
    exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩
end Parastrophes.Eq872CubicCounterexample
