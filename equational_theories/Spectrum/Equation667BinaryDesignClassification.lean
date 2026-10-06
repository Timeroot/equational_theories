import equational_theories.Spectrum.Equation667BinaryDesign
import equational_theories.Spectrum.Equation667BinaryFiveCompleteness

/-! Completeness of independent binary data on a five-point design. Every
normalized binary extension is obtained from one uniquely normalized function
on each block. No finiteness assumption on the design is required. -/
namespace Spectrum.E667.BinaryDesign
open Classical
variable {Q I : Type*} (B : I → Set Q) (e : ∀ i, B i ≃ ZMod 5)
    (cover : ∀ x y : Q, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)

include cover

/-- A normalized coefficient on the whole design restricts to the explicit
five-point formula on each block. -/
theorem local_complete (C : Q → Q → ZMod 2)
    (hd : ∀ x, C x x = 0) (hc : BinaryExtensions.Cocycle (base B e) C)
    (i : I) (a b : ZMod 5) :
    C (point B e i a) (point B e i b) =
      BinaryFive.cocycle (fun k => C (point B e i 0) (point B e i (3*k))) a b := by
  apply BinaryFive.normalized_complete (fun a b => C (point B e i a) (point B e i b))
  · intro k; exact hd _
  · intro x y
    simpa only [base_map B e cover] using hc (point B e i x) (point B e i y)

/-- Every normalized cocycle arises from independent block functions. -/
theorem complete (C : Q → Q → ZMod 2)
    (hd : ∀ x, C x x = 0) (hc : BinaryExtensions.Cocycle (base B e) C) :
    ∃ v : I → ZMod 5 → ZMod 2, (∀ i, v i 0 = 0) ∧ C = coefficient B e v := by
  let v := fun i k => C (point B e i 0) (point B e i (3*k))
  refine ⟨v, ?_, ?_⟩
  · intro i; simpa [v] using hd (point B e i 0)
  · funext x y
    by_cases hxy : x = y
    · subst y; rw [hd, coefficient_diag]
    · obtain ⟨i,hi,_⟩ := cover x y hxy
      let a := e i ⟨x,hi.1⟩
      let b := e i ⟨y,hi.2⟩
      have ha : point B e i a = x := by simp only [point, a, Equiv.symm_apply_apply]
      have hb : point B e i b = y := by simp only [point, b, Equiv.symm_apply_apply]
      rw [← ha, ← hb, coefficient_map B e v cover]
      exact local_complete B e cover C hd hc i a b

/-- Fixing the value at zero removes exactly the redundant constant bit
on each block. No other identifications occur on the labelled carrier. -/
theorem coefficient_injective (v w : I → ZMod 5 → ZMod 2)
    (hv : ∀ i, v i 0 = 0) (hw : ∀ i, w i 0 = 0)
    (he : coefficient B e v = coefficient B e w) : v = w := by
  funext i k
  have hh := congrFun (congrFun he (point B e i 0)) (point B e i (3*k))
  rw [coefficient_map B e v cover, coefficient_map B e w cover] at hh
  have hk : (2 : ZMod 5) * (3*k) - 0 = k := by ring_nf; reduce_mod_char
  simpa only [BinaryFive.cocycle, hk, hv, hw, zero_add] using hh

abbrev NormalizedData (I : Type*) := I → {v : ZMod 5 → ZMod 2 // v 0 = 0}
abbrev NormalizedCocycles := {C : Q → Q → ZMod 2 //
  (∀ x, C x x = 0) ∧ BinaryExtensions.Cocycle (base B e) C}

/-- A full parametrization, with four independent bits per design block. -/
noncomputable def dataEquiv : NormalizedData I ≃ NormalizedCocycles B e :=
  Equiv.ofBijective (fun v => ⟨coefficient B e (fun i => (v i).val),
    coefficient_diag B e _,
    ((BinaryExtensions.law_iff (base B e) _).mp (law B e _ cover)).2⟩) (by
      constructor
      · intro v w hh
        have hvw := coefficient_injective B e cover
          (fun i => (v i).val) (fun i => (w i).val)
          (fun i => (v i).property) (fun i => (w i).property)
          (congrArg Subtype.val hh)
        funext i
        exact Subtype.ext (congrFun hvw i)
      · intro C
        obtain ⟨v,hv,he⟩ := complete B e cover C.val C.property.1 C.property.2
        exact ⟨fun i => ⟨v i,hv i⟩, Subtype.ext he.symm⟩)

/-- The labelled normalized extension count is exactly 2^(4b).
This is a count of operations, not of isomorphism classes. -/
theorem normalized_count [Finite I] :
    Nat.card (NormalizedCocycles B e) = 2 ^ (4 * Nat.card I) := by
  rw [← Nat.card_congr (dataEquiv B e cover)]
  letI := Fintype.ofFinite I
  have hn : Fintype.card {v : ZMod 5 → ZMod 2 // v 0 = 0} = 16 := by decide +kernel
  simp only [NormalizedData, Nat.card_eq_fintype_card, Fintype.card_fun, hn]
  rw [pow_mul]
  rfl

spectrum_assert normalized_count complete
spectrum_assert local_complete complete
spectrum_assert complete complete
spectrum_assert coefficient_injective complete
end Spectrum.E667.BinaryDesign
