import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import equational_theories.Equations.All

/-! E1483 and E1486 have no nontrivial idempotent models, even on infinite
carriers. Thus idempotent PBD gluing cannot supply their missing orders.
See `docs/open_spectra_survey_20260927.md`. -/

namespace Spectrum.WeakCentralIdempotent

theorem collapse1483 {G : Type*} [Magma G] (h : Equation1483 G)
    (hi : ∀ x : G, x ◇ x = x) : Subsingleton G := by
  have cube (x y : G) : x ◇ (x ◇ (x ◇ y)) = x := by
    simpa only [hi] using (h x x y).symm
  have bridge (x y : G) : (x ◇ (x ◇ y)) ◇ (x ◇ y) = x ◇ y := by
    simpa only [hi] using (h (x ◇ y) x y).symm
  have square (x y : G) : x ◇ (x ◇ y) = x := by
    have hh := bridge x (x ◇ y)
    rw [cube, cube] at hh
    exact hh.symm
  have proj (x y : G) : x ◇ y = x := by
    have hh := bridge x y
    rw [square, square] at hh
    exact hh.symm
  exact ⟨fun x y => by simpa only [proj] using h x y x⟩

theorem collapse1486 {G : Type*} [Magma G] (h : Equation1486 G)
    (hi : ∀ x : G, x ◇ x = x) : Subsingleton G := by
  apply collapse1483 (hi := hi)
  intro x y z
  simpa only [hi] using h x y (y ◇ z)

spectrum_assert collapse1483 complete
spectrum_assert collapse1486 complete
/-- info: 'Spectrum.WeakCentralIdempotent.collapse1483' does not depend on any axioms -/
#guard_msgs in
#print axioms collapse1483
/-- info: 'Spectrum.WeakCentralIdempotent.collapse1486' does not depend on any axioms -/
#guard_msgs in
#print axioms collapse1486
end Spectrum.WeakCentralIdempotent
