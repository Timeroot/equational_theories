import equational_theories.Parastrophes.DivisionTerms
import equational_theories.Superposition
import equational_theories.Parastrophes.Catalogue
import equational_theories.Spectrum.Equation1719Twist

/-! The established semisymmetric twist of E1719 is a quasigroup on every carrier. -/
namespace Parastrophes.Catalogue
open FreeMagma

/-- The semisymmetric isotope and its twisting permutation recover all translations. -/
@[parastrophe_result] theorem quasigroup1719 : QuasigroupLaw .all Law1719 := by
  intro G M _ h
  letI : Magma G := M
  have hE := (@Law1719.models_iff G M).mp h
  let S : G → G := fun x => M.op x x
  have hS (x : G) : S (S (S x)) = x := Spectrum.SemisymmetricTwist.square_three hE x
  have hSb : Function.Bijective S :=
    ⟨fun a b he => (hS a).symm.trans ((congrArg (fun x => S (S x)) he).trans (hS b)),
      fun x => ⟨S (S x), hS x⟩⟩
  let T : Magma G := ⟨fun x y => M.op (S x) y⟩
  have hT :=
    (@Law14.models_iff G T).mpr (fun x y => hE x y)
  have hQ := quasigroup14 G T trivial hT
  constructor
  · intro x
    have hr := hQ.1 (S (S x))
    change Function.Bijective (fun z => M.op (S (S (S x))) z) at hr
    simpa only [hS] using hr
  · intro y
    have hb := (hQ.2 y).comp (hSb.comp hSb)
    change Function.Bijective (fun x => M.op (S (S (S x))) y) at hb
    simpa only [hS] using hb

/-- Squaring the right product gives E880's left division. The inverse
calculation is already present inside the proof of E880 implying E4647. -/
@[parastrophe_result] theorem left_term880 :
    UniformTermWitness .all Law880 .left ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h880 := (@Law880.models_iff G M).mp h
  have e9 (x y : G) : y ◇ ((x ◇ y) ◇ (x ◇ y)) = x := (h880 x y).symm
  have e11 (x y : G) : ((y ◇ x) ◇ (y ◇ x)) ◇ (y ◇ y) = x := superpose e9 e9
  have e12 (x y : G) : (y ◇ x) ◇ (y ◇ x) = (y ◇ y) ◇ (x ◇ x) := superpose e9 e11
  have e19 (x y : G) : ((x ◇ y) ◇ x) ◇ ((x ◇ y) ◇ x) = y := superpose e11 e12
  exact ⟨fun x y => e9 y x, fun x y => e19 x y⟩

/-- Both explicit division terms prove unrestricted quasigroupness of E880. -/
@[parastrophe_result] theorem quasigroup880 : QuasigroupLaw .all Law880 := by
  intro G M _ h
  exact quasigroup_of_divisions (left_term880 G M trivial h) (right_term880 G M trivial h)

end Parastrophes.Catalogue
