import equational_theories.Spectrum.InvolutionRoots
import equational_theories.Spectrum.Status

/-! Commutative E907 magmas are exactly Steiner quasigroups. In particular,
nonempty finite commutative models have odd order. This does not classify
arbitrary E907 magmas. See `docs/open_spectra_survey_20260927.md`. -/

namespace Spectrum.E907

variable {G : Type*} [Magma G]

theorem idempotent_of_commutative (h : Equation907 G)
    (hc : ∀ x y : G, x ◇ y = y ◇ x) (a : G) : a ◇ a = a := by
  let s := a ◇ a
  let t := s ◇ s
  have hat : a ◇ t = a := (h a a).symm
  have ht : t = a ◇ s := by
    calc
      t = a ◇ ((a ◇ t) ◇ (t ◇ a)) := h t a
      _ = a ◇ s := by rw [hc t a, hat]
  change s = a
  calc
    s = s ◇ (t ◇ t) := h s s
    _ = s ◇ ((s ◇ a) ◇ (a ◇ s)) := by rw [ht, hc s a]
    _ = a := (h a s).symm

theorem involution_of_commutative (h : Equation907 G)
    (hc : ∀ x y : G, x ◇ y = y ◇ x) (a x : G) : a ◇ (a ◇ x) = x := by
  have hh := (h x a).symm
  rwa [hc x a, idempotent_of_commutative h hc] at hh

/-- Commutative E907 operations are exactly Steiner quasigroups. -/
theorem commutative_iff (hc : ∀ x y : G, x ◇ y = y ◇ x) :
    Equation907 G ↔ (∀ x : G, x ◇ x = x) ∧ (∀ x y : G, x ◇ (x ◇ y) = y) := by
  constructor
  · intro h
    exact ⟨idempotent_of_commutative h hc, involution_of_commutative h hc⟩
  · rintro ⟨hi, hh⟩ x y
    rw [hc x y, hi, hh]

/-- A nonempty commutative finite E907 model has odd order. -/
theorem odd_order {n : ℕ} [Magma (Fin n)] (hn : 0 < n) (h : Equation907 (Fin n))
    (hc : ∀ x y : Fin n, x ◇ y = y ◇ x) : Odd n := by
  classical
  let a : Fin n := ⟨0, hn⟩
  let f : Equiv.Perm (Fin n) := ⟨fun x => a ◇ x, fun x => a ◇ x,
    involution_of_commutative h hc a, involution_of_commutative h hc a⟩
  have hf (x) : f (f x) = x := involution_of_commutative h hc a x
  have unique_fixed (x : Fin n) (hx : f x = x) : x = a := by
    change a ◇ x = x at hx
    have hh := involution_of_commutative h hc x a
    rw [hc x a, hx, idempotent_of_commutative h hc] at hh
    exact hh
  have hcfix : Fintype.card (InvolutionRoots.Fixed f) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    exact ⟨⟨a, idempotent_of_commutative h hc a⟩,
      fun x => Subtype.ext (unique_fixed x x.property)⟩
  have hcard := InvolutionRoots.card_decompose f hf
  simp only [hcfix, Fintype.card_fin] at hcard
  exact ⟨Fintype.card (InvolutionRoots.Asc f), by omega⟩

spectrum_assert commutative_iff complete
spectrum_assert odd_order complete
/-- info: 'Spectrum.E907.commutative_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms commutative_iff
/-- info: 'Spectrum.E907.odd_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_order
end Spectrum.E907
