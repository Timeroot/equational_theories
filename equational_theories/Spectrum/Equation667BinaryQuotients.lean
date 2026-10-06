import equational_theories.Spectrum.Equation667BinaryExtensions
import Mathlib.Data.Fintype.Sigma

/-! Coordinate-free completeness of the binary cocycle description. Any
surjective homomorphism with two-element fibers can be put in this form. -/
namespace Spectrum.E667.BinaryExtensions

/-- Every finite E667 quotient with two-element fibers is a binary cocycle
extension, with the prescribed quotient map as first-coordinate projection. -/
theorem quotient_coordinates {A Q : Type*} [Magma A] [Finite A]
    (hA : Equation667 A) (q : Q → Q → Q) (π : A → Q)
    (hs : Function.Surjective π) (hom : ∀ x y, π (x ◇ y) = q (π x) (π y))
    (hf : ∀ b, Nat.card {x : A // π x = b} = 2) :
    ∃ C : Q → Q → ZMod 2, @Equation667 Q ⟨q⟩ ∧ Cocycle q C ∧
      ∃ E : A ≃ Q × ZMod 2, (∀ a, (E a).1 = π a) ∧
        ∀ x y, E (x ◇ y) = op q C (E x) (E y) := by
  classical
  letI : Finite Q := Finite.of_surjective π hs
  letI (b : Q) : Fintype {x : A // π x = b} := Fintype.ofFinite _
  let ef (b : Q) : {x : A // π x = b} ≃ ZMod 2 :=
    Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hf b)
  let E : A ≃ Q × ZMod 2 :=
    (Equiv.sigmaFiberEquiv π).symm.trans (Equiv.sigmaEquivProdOfEquiv ef)
  have ep (a : A) : (E a).1 = π a := rfl
  have eps (z : Q × ZMod 2) : π (E.symm z) = z.1 := by rw [← ep, E.apply_symm_apply]
  let M : Magma (Q × ZMod 2) := (inferInstance : Magma A).relabel E
  let g : Q → Q → ZMod 2 → ZMod 2 → ZMod 2 := fun i j a b => (M.op (i,a) (j,b)).2
  have hop : M.op = generalOp q g := by
    funext x y
    apply Prod.ext
    · change (E (E.symm x ◇ E.symm y)).1 = q x.1 y.1
      rw [ep, hom, eps, eps]
    · rfl
  have back (x y : Q × ZMod 2) : E.symm (M.op x y) = E.symm x ◇ E.symm y :=
    E.symm_apply_apply _
  have hm : @Equation667 (Q × ZMod 2) ⟨generalOp q g⟩ := by
    intro x y
    apply E.symm.injective
    change E.symm x = E.symm (generalOp q g y
      (generalOp q g x (generalOp q g (generalOp q g x x) y)))
    simpa only [← hop, back] using hA (E.symm x) (E.symm y)
  let C := fun i j => g i j 0 0
  have hg : generalOp q g = op q C := every_fiber_extension q g hm
  have hlaw : @Equation667 (Q × ZMod 2) ⟨op q C⟩ := by
    intro x y
    have hh := hm x y
    change x = generalOp q g y (generalOp q g x (generalOp q g (generalOp q g x x) y)) at hh
    simpa only [hg] using hh
  have hc := (law_iff q C).mp hlaw
  refine ⟨C,hc.1,hc.2,E,ep,?_⟩
  intro x y
  rw [← hg, ← hop]
  change E (x ◇ y) = E (E.symm (E x) ◇ E.symm (E y))
  simp only [E.symm_apply_apply]

spectrum_assert quotient_coordinates complete
end Spectrum.E667.BinaryExtensions
