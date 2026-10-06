import equational_theories.Spectrum.Equation667BinaryFiveIsomorphism
import equational_theories.Spectrum.Equation667BinaryQuotients
import equational_theories.Spectrum.Equation667Quotients

/-! Classification of arbitrary two-point-fiber extensions of the five-point
mean algebra, not just extensions already supplied in affine coordinates. -/
namespace Spectrum.E667.BinaryFive

/-- Every finite E667 operation over the fixed five-point quotient, with
arbitrary two-point Latin blocks, is isomorphic to one of the three normal forms. -/
theorem classify_extension (g : ZMod 5 → ZMod 5 → ZMod 2 → ZMod 2 → ZMod 2)
    (h : @Equation667 Carrier ⟨BinaryExtensions.generalOp base g⟩) :
    ∃ k : Fin 3, ∃ e : Carrier ≃ Carrier, ∀ x y,
      e (BinaryExtensions.generalOp base g x y) = op (representative k) (e x) (e y) := by
  let C := fun i j => g i j 0 0
  have he := BinaryExtensions.every_fiber_extension base g h
  have hC : @Equation667 Carrier ⟨BinaryExtensions.op base C⟩ := by
    intro x y
    have hh := h x y
    change x = BinaryExtensions.generalOp base g y (BinaryExtensions.generalOp base g x
      (BinaryExtensions.generalOp base g (BinaryExtensions.generalOp base g x x) y)) at hh
    simpa only [he] using hh
  let d := fun i => C i i
  let N := BinaryExtensions.gauge base C d
  have hN : @Equation667 Carrier ⟨BinaryExtensions.op base N⟩ :=
    BinaryExtensions.gauge_law base C d hC
  have hd : ∀ i, N i i = 0 := BinaryExtensions.normalize_diag base base_idem C
  have hc : BinaryExtensions.Cocycle base N := (BinaryExtensions.law_iff base N).mp hN |>.2
  let v := fun i => N 0 (3*i)
  have hn : BinaryExtensions.op base N = op v := by
    funext x y
    apply Prod.ext
    · rfl
    · change x.2 + y.2 + N x.1 y.1 = x.2 + y.2 + cocycle v x.1 y.1
      rw [normalized_complete N hd hc]
  obtain ⟨k,E,hE⟩ := exists_representative v
  refine ⟨k, (BinaryExtensions.shiftEquiv d).trans E, ?_⟩
  intro x y
  change E (BinaryExtensions.shift d (BinaryExtensions.generalOp base g x y)) =
    op (representative k) (E (BinaryExtensions.shift d x)) (E (BinaryExtensions.shift d y))
  rw [he, BinaryExtensions.shift_hom]
  change E (BinaryExtensions.op base N (BinaryExtensions.shift d x) (BinaryExtensions.shift d y)) = _
  rw [hn]
  exact hE _ _

/-- Coordinate-free version: any ten-element E667 magma mapping onto the
five-point mean algebra belongs to exactly the three classified extension types. -/
theorem classify_quotient {A : Type*} [Magma A] [Finite A]
    (hA : Equation667 A) (hcard : Nat.card A = 10)
    (π : A → ZMod 5) (hs : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = base (π x) (π y)) :
    ∃ k : Fin 3, ∃ e : A ≃ Carrier, ∀ x y,
      e (x ◇ y) = op (representative k) (e x) (e y) := by
  classical
  letI : Magma (ZMod 5) := ⟨base⟩
  have hK : Equation667 (ZMod 5) := by
    intro i j
    change i = base j (base i (base (base i i) j))
    rw [base_idem, base_law]
  have hf (b : ZMod 5) : Nat.card {x : A // π x = b} = 2 := by
    have hh := Quotients.card_eq_mul_fiber hA hK π hom hs b
    rw [hcard, Nat.card_zmod] at hh
    omega
  obtain ⟨C,hq,hc,E,_,he⟩ := BinaryExtensions.quotient_coordinates hA base π hs hom hf
  have hm : @Equation667 Carrier ⟨BinaryExtensions.op base C⟩ :=
    (BinaryExtensions.law_iff base C).mpr ⟨hq,hc⟩
  obtain ⟨k,F,hF⟩ := classify_extension (fun i j a b => a+b+C i j) hm
  refine ⟨k,E.trans F,?_⟩
  intro x y
  exact (congrArg F (he x y)).trans (hF (E x) (E y))

spectrum_assert classify_extension complete
spectrum_assert classify_quotient complete
end Spectrum.E667.BinaryFive
