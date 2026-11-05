import equational_theories.Parastrophes.FiniteSolutions
import equational_theories.Parastrophes.FiniteQuasigroups

/-! Fixed division terms from cyclically rotating functional factorizations.
A factor need not itself be a translation: squaring and other unary polynomials
may be rotated as well. The inverse terms do not depend on the finite order. -/
namespace Parastrophes
open Law FreeMagma

/-- On a finite carrier, a composition equal to the identity can be rotated. -/
theorem rotate_finite {G : Type*} [Finite G] {f g : G → G}
    (h : ∀ x, f (g x) = x) : ∀ x, g (f x) = x := by
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr
    (fun x => ⟨g x, h x⟩)
  intro x
  exact hi (h (f x))

/-- A uniform left inverse of a finite translation is its two-sided inverse. -/
theorem uniform_left_of_inverse_fin {L t}
    (hs : ∀ (G : Type) (M : Magma G), Finite G → @satisfies _ G M L →
      ∀ x y, (termMagma M t).op x (M.op x y) = y) :
    UniformTermWitness .fin L .left t := by
  intro G M hG h
  letI : Finite G := hG
  have hh := hs G M hG h
  exact ⟨fun x => rotate_finite (hh x), hh⟩

namespace Catalogue

/-- Rotate the factorization in E1525 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term1525_fin_rotation :
    UniformTermWitness .fin Law1525 .left (((Lf 0 ⋆ Lf 0) ⋆ Lf 1) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law1525.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y y) (M.op y x))) (g := fun x => (M.op x x))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2291 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2291_fin_rotation :
    UniformTermWitness .fin Law2291 .left ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0))) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2291.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y x) y)) (g := fun x => (M.op x (M.op x x)))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2294 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2294_fin_rotation :
    UniformTermWitness .fin Law2294 .left ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 0)) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2294.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y x) y)) (g := fun x => (M.op x (M.op x y)))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2301 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2301_fin_rotation :
    UniformTermWitness .fin Law2301 .left ((Lf 1 ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 0))) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2301.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y x) y)) (g := fun x => (M.op x (M.op y x)))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2328 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2328_fin_rotation :
    UniformTermWitness .fin Law2328 .left (((Lf 0 ⋆ Lf 1) ⋆ Lf 0) ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0)) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2328.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y (M.op y x)) y)) (g := fun x => (M.op x x))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2497 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2497_fin_rotation :
    UniformTermWitness .fin Law2497 .left (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 0) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2497.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y x) y)) (g := fun x => (M.op (M.op x x) y))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2504 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2504_fin_rotation :
    UniformTermWitness .fin Law2504 .left (((Lf 1 ⋆ Lf 0) ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2504.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y x) y)) (g := fun x => (M.op (M.op x y) x))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2531 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2531_fin_rotation :
    UniformTermWitness .fin Law2531 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2531.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op y x) y)) (g := fun x => (M.op (M.op y x) x))
    (fun x => (hm x y).symm) x

/-- Rotate the factorization in E2903 to read off a fixed left inverse. -/
@[parastrophe_result] theorem left_term2903_fin_rotation :
    UniformTermWitness .fin Law2903 .left (((Lf 1 ⋆ Lf 0) ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 0)) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2903.models_iff G M).mp h
  exact rotate_finite (f := fun x => (M.op (M.op (M.op y x) y) y)) (g := fun x => (M.op x x))
    (fun x => (hm x y).symm) x

/-- Rotating E2734 supplies a square root term. Substituting that root into
the inverse of a square-indexed row gives division at every row. -/
@[parastrophe_result] theorem left_term2734_fin_rotation :
    UniformTermWitness .fin Law2734 .left
      ((Lf 1 ⋆ (((Lf 0 ⋆ Lf 0) ⋆ Lf 0) ⋆ Lf 0)) ⋆
        (Lf 1 ⋆ (((Lf 0 ⋆ Lf 0) ⋆ Lf 0) ⋆ Lf 0))) := by
  apply uniform_left_of_inverse_fin
  intro G M hG h y x
  letI : Finite G := hG
  have hm := (@Law2734.models_iff G M).mp h
  have rot (a z : G) :
      M.op (M.op (M.op (M.op a a) z) a) (M.op (M.op (M.op a a) z) a) = z :=
    rotate_finite (f := fun z => M.op (M.op (M.op a a) z) a)
      (g := fun z => M.op z z) (fun z => (hm z a).symm) z
  let r := M.op (M.op (M.op y y) y) y
  have hr : M.op r r = y := rot y y
  change M.op (M.op (M.op y x) r) (M.op (M.op y x) r) = x
  simpa only [hr] using rot r x

/-- Three successive left divisions give right division in finite E464.
The expression expands to a fixed term, independent of the carrier's order. -/
@[parastrophe_result] theorem right_term464_fin_rotation :
    UniformTermWitness .fin Law464 .right
      (let u : FreeMagma (Fin 2) := Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))
       let v := u ⋆ (u ⋆ (u ⋆ Lf 0))
       v ⋆ (v ⋆ (v ⋆ Lf 0))) := by
  intro G M hG h
  have hQ := quasigroup464_fin G M hG h
  have hD := left_term464_fin G M hG h
  let D := termMagma M (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))
  have hi (x y : G) : D.op (M.op x y)
      (D.op (M.op x y) (D.op (M.op x y) y)) = x := by
    let c := M.op x y
    have he : M.op c (M.op c (M.op c x)) = y :=
      (hQ.1 x).1 ((@Law464.models_iff G M).mp h c x).symm
    change D.op c (D.op c (D.op c y)) = x
    rw [← he, hD.2, hD.2, hD.2]
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := (hQ.2 y).2 x
    exact congrArg (fun z => M.op z y) (hi a y)
  · exact hi

end Catalogue
end Parastrophes
