import equational_theories.Parastrophes.RotatedDivisionTerms

/-! Explicit square-root terms replace a size-dependent inverse permutation. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

/-- The inverse law for E467's left division, evaluated on the diagonal,
gives a cube-shaped square root: `(x*x)*((x*x)*(x*x)) = x`. -/
theorem square_root467 {G : Type} (M : Magma G) (hG : Finite G)
    (h : @satisfies _ G M Law467) (x : G) :
    M.op (M.op x x) (M.op (M.op x x) (M.op x x)) = x :=
  (left_term467_fin G M hG h).2 x x

/-- Right division is two left divisions followed by the fixed square-root term.
The dual gives the formerly missing uniform left division of E3140. -/
@[parastrophe_result] theorem right_term467_fin :
    UniformTermWitness .fin Law467 .right
      (let u : FreeMagma (Fin 2) := Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))
       let v := u ⋆ (u ⋆ (Lf 0 ⋆ Lf 0))
       v ⋆ (v ⋆ v)) := by
  intro G M hG h
  have hQ := quasigroup467_fin G M hG h
  have hD := left_term467_fin G M hG h
  let D := termMagma M (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))
  have hi (x y : G) :
      let v := D.op (M.op x y) (D.op (M.op x y) y)
      M.op v (M.op v v) = x := by
    let c := M.op x y
    have he : M.op c (M.op c (M.op x x)) = y :=
      (hQ.1 x).1 ((@Law467.models_iff G M).mp h c x).symm
    have hv : D.op c (D.op c y) = M.op x x := by
      rw [← he, hD.2, hD.2]
    change M.op (D.op c (D.op c y))
      (M.op (D.op c (D.op c y)) (D.op c (D.op c y))) = x
    rw [hv]
    exact square_root467 M hG h x
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := (hQ.2 y).2 x
    exact congrArg (fun z => M.op z y) (hi a y)
  · exact hi

/-- A square root in finite E1516: put `q(x) = x*(x*x)` and use
`q(x)*(q(x)*x)`. The proof rotates the law at square-indexed translations. -/
theorem square_root1516 {G : Type} (M : Magma G) (hG : Finite G)
    (h : @satisfies _ G M Law1516) (x : G) :
    let q := M.op x (M.op x x)
    let r := M.op q (M.op q x)
    M.op r r = x := by
  letI : Finite G := hG
  have hm := (@Law1516.models_iff G M).mp h
  have hQ := quasigroup1516_fin G M hG h
  have rot (a z : G) :
      M.op (M.op (M.op a a) z) (M.op (M.op (M.op a a) z) a) = z :=
    rotate_finite (f := fun z => M.op (M.op a a) z)
      (g := fun z => M.op z (M.op z a)) (fun z => (hm z a).symm) z
  have inv (y : G) :
      let s := M.op y y
      let q := M.op s (M.op s s)
      M.op q (M.op q s) = y := by
    let s := M.op y y
    have he : M.op (M.op s s) y = M.op s (M.op s s) :=
      (hQ.1 (M.op s s)).1 ((rot y s).trans (hm s s))
    change M.op (M.op s (M.op s s))
      (M.op (M.op s (M.op s s)) s) = y
    rw [← he]
    exact rot s y
  exact rotate_finite (f := fun x =>
    M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))
    (g := fun x => M.op x x) inv x

/-- E1516 has a fixed left-division term: use its uniform square root to
replace the square-indexed translation in the original law. -/
@[parastrophe_result] theorem left_term1516_fin :
    UniformTermWitness .fin Law1516 .left
      (let q : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 0 ⋆ Lf 0)
       let r := q ⋆ (q ⋆ Lf 0)
       Lf 1 ⋆ (Lf 1 ⋆ r)) := by
  intro G M hG h
  letI : Finite G := hG
  have hm := (@Law1516.models_iff G M).mp h
  have hi (x y : G) :
      let q := M.op x (M.op x x)
      let r := M.op q (M.op q x)
      M.op x (M.op y (M.op y r)) = y := by
    let q := M.op x (M.op x x)
    let r := M.op q (M.op q x)
    have hr : M.op r r = x := square_root1516 M hG h x
    simpa only [hr] using (hm y r).symm
  exact ⟨hi, fun x => rotate_finite (hi x)⟩

/-- Right division in E1516 is the square of two successive left divisions. -/
@[parastrophe_result] theorem right_term1516_fin :
    UniformTermWitness .fin Law1516 .right
      (let q : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 0 ⋆ Lf 0)
       let r := q ⋆ (q ⋆ Lf 0)
       let u := Lf 1 ⋆ (Lf 1 ⋆ r)
       let v := u ⋆ (u ⋆ r)
       v ⋆ v) := by
  intro G M hG h
  have hQ := quasigroup1516_fin G M hG h
  let t : FreeMagma (Fin 2) :=
    let q := Lf 0 ⋆ (Lf 0 ⋆ Lf 0)
    let r := q ⋆ (q ⋆ Lf 0)
    Lf 1 ⋆ (Lf 1 ⋆ r)
  let D := termMagma M t
  have hD : IsDivision .left M D := left_term1516_fin G M hG h
  have hi (x y : G) :
      let v := D.op (M.op x y) (D.op (M.op x y) y)
      M.op v v = x := by
    let q := M.op x (M.op x x)
    let r := M.op q (M.op q x)
    have hr : M.op r r = x := square_root1516 M hG h x
    let c := M.op x y
    have he : M.op c (M.op c r) = y := by
      apply (hQ.1 x).1
      have e := ((@Law1516.models_iff G M).mp h c r).symm
      rw [hr] at e
      exact e
    have hv : D.op c (D.op c y) = r := by rw [← he, hD.2, hD.2]
    change M.op (D.op c (D.op c y)) (D.op c (D.op c y)) = x
    rw [hv]
    exact hr
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := (hQ.2 y).2 x
    exact congrArg (fun z => M.op z y) (hi a y)
  · exact hi

end Parastrophes.Catalogue
