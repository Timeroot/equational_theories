import equational_theories.Parastrophes.ImageBasis
import equational_theories.Parastrophes.Equation872ImageBasis
import equational_theories.Parastrophes.Equation695Image
import equational_theories.Parastrophes.Equation1370Image

/-! Shorter multi-equation descriptions, including images whose single-equation
characterization is still open. Finite and arbitrary carriers are distinguished. -/
namespace Parastrophes.ImageBasisCatalogue
open Law FreeMagma

private def c (t : FreeMagma Nat) := t ⋆ ((t ⋆ t) ⋆ t)

def cross872 : NatMagmaLaw := ⟨Lf 0, Lf 1 ⋆ (c (Lf 0) ⋆ (Lf 1 ⋆ Lf 0))⟩
def inverse872 : NatMagmaLaw :=
  ⟨c (Lf 0 ⋆ Lf 1) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1)), Lf 1⟩
def coreSquare872 : NatMagmaLaw := ⟨c (c (Lf 0)), Lf 0 ⋆ Lf 0⟩

private theorem cross872_iff {G : Type} (D : Magma G) :
    @satisfies _ G D cross872 ↔ ∀ x y,
      x = D.op y (D.op (Eq872Image.core D x) (D.op y x)) := by
  constructor
  · intro h x y; exact h (fun n => if n = 0 then x else y)
  · intro h v; exact h (v 0) (v 1)

private theorem inverse872_iff {G : Type} (D : Magma G) :
    @satisfies _ G D inverse872 ↔ ∀ x y,
      D.op (Eq872Image.core D (D.op x y)) (D.op x (D.op x y)) = y := by
  constructor
  · intro h x y; exact h (fun n => if n = 0 then x else y)
  · intro h v; exact h (v 0) (v 1)

private theorem coreSquare872_iff {G : Type} (D : Magma G) :
    @satisfies _ G D coreSquare872 ↔ ∀ x,
      Eq872Image.core D (Eq872Image.core D x) = D.op x x := by
  constructor
  · intro h x; exact h (fun _ => x)
  · intro h v; exact h (v 0)

/-- Put c(x)=x*((x*x)*x). The two identities are x=x*c(x) and
x=y*(c(x)*(y*x)). Their conjunction exactly characterizes the finite image;
this is not a positive answer to the one-equation question. -/
@[parastrophe_basis] theorem left872_fin :
    CharacterizesBasis .fin Law872 .left [Law614, cross872] := by
  intro G D hG
  letI : Finite G := hG
  simpa [ Law614.models_iff,
    cross872_iff, Eq872Image.Basis] using Eq872Image.characterizes_fin D

/-- An alternative pair: the cross identity and c(c(x))=x*x. -/
@[parastrophe_basis] theorem left872_fin_coreSquare :
    CharacterizesBasis .fin Law872 .left [cross872, coreSquare872] := by
  intro G D hG
  letI : Finite G := hG
  simpa [
    cross872_iff, coreSquare872_iff] using Eq872Image.characterizes_core_square_fin D

/-- Three identities characterize the image on arbitrary carriers. The third
identity supplies the inverse equation that finiteness makes automatic. -/
@[parastrophe_basis] theorem left872_all :
    CharacterizesBasis .all Law872 .left [Law614, cross872, inverse872] := by
  intro G D _
  simpa [ Law614.models_iff,
    cross872_iff, inverse872_iff, Eq872Image.CompleteBasis, Eq872Image.Basis, and_assoc]
    using Eq872Image.characterizes_all D

def rightUnit695 : NatMagmaLaw :=
  ⟨Lf 0 ⋆ ((Lf 1 ⋆ (Lf 1 ⋆ Lf 1)) ⋆ Lf 1), Lf 0⟩

private theorem basis695_iff {G : Type} (D : Magma G) :
    (∀ t ∈ [Law1155, rightUnit695], @satisfies _ G D t) ↔ Eq695Image.Basis D := by
  simp [ Law1155.models_iff,
    Eq695Image.Basis, and_congr_right_iff]
  intro _
  constructor
  · intro h x z; exact h (fun n => if n = 0 then x else z)
  · intro h v; exact h (v 0) (v 1)

/-- A shorter alternative to the known eight-operation single equation:
E1155 and a definable right identity. -/
@[parastrophe_basis] theorem left695_all :
    CharacterizesBasis .all Law695 .left [Law1155, rightUnit695] := by
  intro G D _
  exact (basis695_iff D).trans ((Eq695Image.iff_basis D).symm.trans
    (Catalogue.left_characterizes695_all_long G D trivial))

/-- The same two equations describe the image of the E1710 models admitting
left division, without asserting that all E1710 models admit it. -/
@[parastrophe_basis] theorem left1710_all :
    CharacterizesBasis .all Law1710 .left [Law1155, rightUnit695] := by
  intro G D _
  exact (basis695_iff D).trans ((Eq695Image.iff_basis D).symm.trans
    (Catalogue.left_characterizes1710_all_partial G D trivial))

def cross1370 : NatMagmaLaw :=
  let t := Lf 2 ⋆ Lf 1
  ⟨Lf 0, Lf 1 ⋆ (((t ⋆ t) ⋆ Lf 1) ⋆ Lf 0)⟩

/-- E127 and a six-operation identity give a shorter description than the
known expanded single identity for this image. -/
@[parastrophe_basis] theorem left1370_all :
    CharacterizesBasis .all Law1370 .left [Law127, cross1370] := by
  intro G D _
  have hb : (∀ t ∈ [Law127, cross1370], @satisfies _ G D t) ↔ Eq1370Image.Basis D := by
    simp [ Law127.models_iff,
      Eq1370Image.Basis, and_congr_right_iff]
    intro _
    constructor
    · intro h x y z
      exact h (fun n => if n = 0 then x else if n = 1 then y else z)
    · intro h v; exact h (v 0) (v 1) (v 2)
  exact hb.trans ((Eq1370Image.iff_basis D).symm.trans
    (Catalogue.left_characterizes1370_all_long G D trivial))

end Parastrophes.ImageBasisCatalogue
