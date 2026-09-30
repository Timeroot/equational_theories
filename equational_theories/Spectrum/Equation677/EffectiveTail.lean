import equational_theories.Spectrum.Equation677.EffectiveTail.Certificate
import equational_theories.Spectrum.Shapes

/-! The effective E677 spectrum bound supplied in PR #6, integrated with the
project's standard models, finite rings, transversal designs, and proof audit. -/
namespace Spectrum.E677.EffectiveTail

/-- Every order from 164475 onward has an E677 model. All certificates are
checked by the Lean kernel; this theorem has no remaining finite obligations. -/
theorem all_large (n : ℕ) (hn : 164475 ≤ n) : Law677.HasModel n :=
  OrderBitmap.Cert.hasModel_of_ge hn

theorem cofinite : CofiniteSpectrum Law677 :=
  ⟨164475, fun n hn => ⟨by omega, all_large n hn⟩⟩

spectrum_assert all_large complete
spectrum_assert cofinite complete
/-- info: 'Spectrum.E677.EffectiveTail.all_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_large
end Spectrum.E677.EffectiveTail

namespace Spectrum

/-- Positive orders recorded by the kernel-checked construction bitmap. -/
def e677CertifiedOrders : Set ℕ :=
  {n | 0 < n ∧ E677.EffectiveTail.OrderBitmap.Cert.certH.testBit n = true}

theorem E677.EffectiveTail.certificate_lower : e677CertifiedOrders ⊆ Law677.spectrum := by
  rintro n ⟨hn, hb⟩
  exact ⟨hn, OrderBitmap.Cert.sound_certH n hb⟩

spectrum_assert E677.EffectiveTail.certificate_lower complete
end Spectrum
