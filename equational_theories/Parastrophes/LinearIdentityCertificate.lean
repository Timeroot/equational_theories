import equational_theories.Parastrophes.AffineIdentityCertificate
import Mathlib.LinearAlgebra.Pi

/-! Identity certificates for linear magmas on finite free modules.
Only one assignment per basis vector of the three-variable space is checked. -/
namespace Parastrophes.LinearIdentityCertificate
open Law FreeMagma AffineIdentityCertificate
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

@[implicit_reducible] def magma (A B : V →ₗ[R] V) : Magma V := ⟨fun x y => A x+B y⟩

def termMap (A B : V →ₗ[R] V) : FreeMagma (Fin 3) → ((Fin 3 → V) →ₗ[R] V)
  | .Leaf i => LinearMap.proj i
  | .Fork a b => A.comp (termMap A B a) + B.comp (termMap A B b)

theorem eval_eq (A B : V →ₗ[R] V) (t : FreeMagma (Fin 3)) (v : Fin 3 → V) :
    @evalInMagma _ V (magma A B) v t = termMap A B t v := by
  induction t with
  | Leaf i => rfl
  | Fork a b ha hb =>
    change A (@evalInMagma _ V (magma A B) v a) +
      B (@evalInMagma _ V (magma A B) v b) = _
    rw [ha, hb]
    rfl

/-- For three-dimensional vectors, nine assignments suffice, regardless of
field size. No commutativity of the two linear operators is required. -/
theorem satisfies_of_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : (ι → R) →ₗ[R] (ι → R)) (t : FreeMagma (Fin 3))
    (h : ∀ i j, @evalInMagma _ _ (magma A B) (Pi.single i (Pi.single j 1)) t =
      (Pi.single i (Pi.single j 1) : Fin 3 → ι → R) 0) :
    @satisfies _ _ (magma A B) (identity t) := by
  have hm : termMap A B t = LinearMap.proj (R := R) (φ := fun _ : Fin 3 => ι → R) 0 := by
    ext i j : 3
    simpa only [← eval_eq, LinearMap.comp_apply, LinearMap.single_apply,
      LinearMap.proj_apply] using h i j
  letI : Magma (ι → R) := magma A B
  intro v
  change v 0 = @evalInMagma _ _ (magma A B) v (fmapFreeMagma Fin.val t)
  rw [← evalInMagma_comp, eval_eq, hm]
  rfl
end Parastrophes.LinearIdentityCertificate
