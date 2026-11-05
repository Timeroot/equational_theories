import equational_theories.Parastrophes.SquareImages

/-!
# The remaining finite uniform-term question for E1518

Uniform left division is equivalent to a uniform unary inverse-square term.
We use a binary term with both inputs identified to express a unary term;
there is no restriction on its size or shape. From a square root r(x), the
left division is y*(r(x)*y). Conversely, left division evaluated at (x,x)
is the inverse square. This is an equivalence of open questions, not a
positive or negative catalogue answer.
-/
namespace Parastrophes.Eq1518Uniform
open FreeMagma

def termDepth {A : Type} : FreeMagma A → ℕ
  | .Leaf _ => 0
  | .Fork t u => max (termDepth t) (termDepth u) + 1

/-- Identifying the two variables gives a completely general unary magma term. -/
def SquareRootWitness (t : FreeMagma (Fin 2)) : Prop :=
  ∀ (G : Type) (M : Magma G), Finite G → @Equation1518 G M → ∀ x,
    M.op ((termMagma M t).op x x) ((termMagma M t).op x x) = x

/-- A candidate unary root produces a candidate division with two more products. -/
def divisionTerm (t : FreeMagma (Fin 2)) : FreeMagma (Fin 2) :=
  Lf 1 ⋆ ((fmapHom (fun _ : Fin 2 => (0 : Fin 2)) t) ⋆ Lf 1)

theorem divisionTerm_eval {G : Type} (M : Magma G) (t : FreeMagma (Fin 2)) (x y : G) :
    (termMagma M (divisionTerm t)).op x y =
      M.op y (M.op ((termMagma M t).op x x) y) := by
  change M.op y (M.op
    (@evalInMagma _ _ M (fun i => if i = 0 then x else y)
      (fmapHom (fun _ : Fin 2 => (0 : Fin 2)) t)) y) = _
  rw [evalInMagma_fmapHom]
  change M.op y (M.op
    (@evalInMagma _ _ M ((fun i : Fin 2 => if i = 0 then x else y) ∘ (fun _ => 0)) t) y) =
    M.op y (M.op (@evalInMagma _ _ M (fun i : Fin 2 => if i = 0 then x else x) t) y)
  simp only [Function.comp_def, Fin.isValue, ↓reduceIte, ite_self]

theorem division_of_root {t : FreeMagma (Fin 2)} (h : SquareRootWitness t) :
    UniformTermWitness .fin Law1518 .left (divisionTerm t) := by
  intro G M hG hm
  letI : Finite G := hG
  have hM := (@Law1518.models_iff G M).mp hm
  have hq := Catalogue.leftQuasigroup1518_fin G M hG hm
  have hr := h G M hG hM
  have he (x y : G) : M.op x ((termMagma M (divisionTerm t)).op x y) = y := by
    rw [divisionTerm_eval]
    simpa only [hr] using (hM y ((termMagma M t).op x x)).symm
  exact ⟨he, fun x y => (hq x).1 (he x (M.op x y))⟩

theorem root_of_division {t : FreeMagma (Fin 2)}
    (h : UniformTermWitness .fin Law1518 .left t) : SquareRootWitness t := by
  intro G M hG hM x
  letI : Finite G := hG
  have hd := h G M hG ((@Law1518.models_iff G M).mpr hM)
  obtain ⟨r, hr⟩ := (Catalogue.square_bijective1518 M hM).2 x
  have hm : M.op x r = x := by
    rw [← hr]
    exact Catalogue.square_mul1518 M hM r
  have he := hd.2 x r
  rw [hm] at he
  rw [he]
  exact hr

/-- This reduces the catalogue question to unary terms without introducing a
period bound or restricting to a particular family of finite models. -/
theorem recovery_iff_squareRoot :
    UniformTermRecovery .fin Law1518 .left ↔
      ∃ t : FreeMagma (Fin 2), SquareRootWitness t := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, root_of_division ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨divisionTerm t, division_of_root ht⟩

end Parastrophes.Eq1518Uniform
