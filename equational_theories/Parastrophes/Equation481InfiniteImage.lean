import equational_theories.Parastrophes.Equation1496ImageObstruction
import equational_theories.Parastrophes.Equation481ImageBasis
import equational_theories.Parastrophes.Equation477Image

/-!
# Infinite obstructions shared by E481 and E477

The twisted-cycle quasigroup already used for E1496 also lies in the actual
left-division images of E481 and E477. Its nonnegative half is a submagma
whose row at the right identity is not onto. Consequently neither image is
equational on arbitrary carriers, even when the source is restricted to
models admitting division.

This also answers the arbitrary-carrier inverse-core search: the cubic map
`c(x)=x*(x*x)` is the upward shift, so no unary multiplication term can invert
it, already in one fixed countable image. A term evaluated at height zero
stays at nonnegative height, while the required preimage has height -1.

The finite single-equation questions remain open. In particular this proof
must not be described as a refutation of a uniform term on finite images.
-/
namespace Parastrophes.Eq481InfiniteImage
open Law FreeMagma Eq1496ImageObstruction TwistedCycleCompletion

/-- The same right-unital crossed quasigroup is also an actual E481 image. -/
theorem source481 (p : TwistedCycleCompletion.Completed) :
    @Equation481 Carrier (source p) :=
  Eq481Image.backward (source p) (division p) (division_symm (isDivision p))
    none (right_unit p) (fun x y => cross p y x)

theorem source477 (p : TwistedCycleCompletion.Completed) :
    @Equation477 Carrier (source p) := fun x y => source481 p x y y

theorem image481 : InImage Law481 .left (division TwistedCycleCompletion.complete) :=
  ⟨source _, (@Law481.models_iff Carrier (source complete)).mpr (source481 _), division_symm (isDivision _)⟩

theorem image477 : InImage Law477 .left (division TwistedCycleCompletion.complete) :=
  ⟨source _, (@Law477.models_iff Carrier (source complete)).mpr (source477 _), division_symm (isDivision _)⟩

theorem no_single481 : ¬ SingleEquation .all Law481 .left :=
  no_singleEquation_of_source ((@Law481.models_iff Carrier (source complete)).mpr (source481 _))

theorem no_single477 : ¬ SingleEquation .all Law477 .left :=
  no_singleEquation_of_source ((@Law477.models_iff Carrier (source complete)).mpr (source477 _))

/-- Every identity inherited from the full image also holds in its bad
submagma. Thus the obstruction excludes arbitrary axiom sets, not only a
single equation. -/
theorem no_equational_axiomatization (L : NatMagmaLaw)
    (hsource : @satisfies _ Carrier (source complete) L) :
    ¬ ∃ laws : Set NatMagmaLaw, ∀ (A : Type) (D : Magma A),
      InImage L .left D ↔ ∀ K ∈ laws, @satisfies _ A D K := by
  rintro ⟨laws, hh⟩
  have hwhole := (hh Carrier (division complete)).mp
    ⟨source complete, hsource, division_symm (isDivision complete)⟩
  have hsub : InImage L .left (subDivision complete) := by
    apply (hh Subcarrier (subDivision complete)).mpr
    intro K hK v
    apply Subtype.val_injective
    rw [sub_eval, sub_eval]
    exact hwhole K hK (fun i => (v i).val)
  obtain ⟨M, _, hd⟩ := hsub
  exact sub_not_leftQuasigroup complete
    (sideQuasigroup_of_division (division_symm hd))

/-- Unary evaluation stays in the nonnegative half of the shifted orbits. -/
theorem term_bounded (t : FreeMagma (Fin 2)) (x : Carrier) (hx : bounded x) :
    bounded ((termMagma (division TwistedCycleCompletion.complete) t).op x x) := by
  have closed (t : FreeMagma (Fin 2)) (v : Fin 2 → Carrier)
      (hv : ∀ i, bounded (v i)) :
      bounded (@evalInMagma _ _ (division TwistedCycleCompletion.complete) v t) := by
    induction t with
    | Leaf i => exact hv i
    | Fork a b ha hb => exact division_bounded _ ha hb
  exact closed t _ (fun _ => by simpa only [ite_self] using hx)

/-- A single countable image refutes every proposed unary inverse of the
cubic map. This is an arbitrary-carrier obstruction, not a finite one. -/
theorem inverse_core_not_term (t : FreeMagma (Fin 2)) :
    Eq477Image.core (division TwistedCycleCompletion.complete)
      ((termMagma (division TwistedCycleCompletion.complete) t).op
        (some (0,0)) (some (0,0))) ≠ some (0,0) := by
  have hb := term_bounded t (some (0,0)) (by change (0 : Int) ≤ 0; omega)
  intro he
  change op _ _ (op _ _ _) = _ at he
  rw [cross] at he
  generalize hz : (termMagma (division TwistedCycleCompletion.complete) t).op
    (some (0,0)) (some (0,0)) = z at he hb
  cases z with
  | none => cases he
  | some z =>
    have hs := congrArg (fun v : Carrier => v.map Prod.snd) he
    simp only [turn, Option.map_some, shift_snd, Option.some.injEq] at hs
    change 0 ≤ z.2 at hb
    omega

/-- This one image does not even admit a term chosen specifically for it
that recovers its left division. Thus the obstruction is stronger than a
failure to find a term uniform over all images. -/
theorem inverse_not_term_definable :
    ¬ ∃ t : FreeMagma (Fin 2),
      IsDivision .left (division complete) (termMagma (division complete) t) := by
  rintro ⟨t, ht⟩
  exact inverse_not_term t
    (congrArg (fun D : Magma Carrier => D.op) (division_unique ht (isDivision complete)))

/-- There is no inverse-core term uniform over arbitrary E481 images. -/
theorem no_uniform_inverse_core481 :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ (A : Type) (D : Magma A),
      InImage Law481 .left D → ∀ x,
      Eq477Image.core D ((termMagma D t).op x x) = x := by
  rintro ⟨t, ht⟩
  exact inverse_core_not_term t (ht Carrier (division complete) image481 _)

/-- E477 is weaker, so the same fixed model refutes uniform recovery there. -/
theorem no_uniform_inverse_core477 :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ (A : Type) (D : Magma A),
      InImage Law477 .left D → ∀ x,
      Eq477Image.core D ((termMagma D t).op x x) = x := by
  rintro ⟨t, ht⟩
  exact inverse_core_not_term t (ht Carrier (division complete) image477 _)

end Parastrophes.Eq481InfiniteImage

namespace Parastrophes.Catalogue

/-- This concerns the image of the E481 models admitting left division;
it does not assert division for every infinite E481 source. -/
@[parastrophe_result] theorem left_noSingleEquation481_all :
    ¬ SingleEquation .all Law481 .left := Eq481InfiniteImage.no_single481

/-- The same obstruction works for the weaker source equation E477. -/
@[parastrophe_result] theorem left_noSingleEquation477_all :
    ¬ SingleEquation .all Law477 .left := Eq481InfiniteImage.no_single477

end Parastrophes.Catalogue
