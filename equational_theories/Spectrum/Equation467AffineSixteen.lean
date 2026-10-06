import equational_theories.Definability.Hom1516
import equational_theories.Spectrum.Status

/-! The existing homogeneous obstruction also excludes affine E467 models
over F16 with an arbitrary constant term. This is a subclass obstruction,
not a nonexistence theorem for all sixteen-element magmas. -/

namespace Spectrum.E467

/-- Subtracting the law at `(0,0)` removes the affine constant. -/
theorem homogenize {R : Type*} [CommRing R] (a b c : R)
    (h : @Equation467 R ⟨fun x y => a*x+b*y+c⟩) :
    @Equation467 R ⟨fun x y => a*x+b*y⟩ := by
  intro x y
  have hxy := h x y
  have hzero := h 0 0
  change x = a*y+b*(a*x+b*(a*x+b*(a*y+b*y)))
  change x = a*y+b*(a*x+b*(a*x+b*(a*y+b*y+c)+c)+c)+c at hxy
  change 0 = a*0+b*(a*0+b*(a*0+b*(a*0+b*0+c)+c)+c)+c at hzero
  linear_combination hxy - hzero

theorem no_affine_F16 (a b c : F16) :
    ¬ @Equation467 F16 ⟨fun x y => a*x+b*y+c⟩ := by
  intro h
  apply Hom467.no_homog_467 (fun x y => a*x+b*y)
  · intro t x y _
    ring
  · exact homogenize a b c h

spectrum_assert no_affine_F16 complete

end Spectrum.E467
