import equational_theories.Spectrum.Generated.BV474_4
import equational_theories.Spectrum.Generated.BV1286_5

/-! Integrated symmetry-broken bit-vector exclusions. Each assembled proof
is checked complete below; total compilation timings are in docs/spectrum_bv.md. -/

namespace Spectrum

theorem not_order_474_4 : ¬ Law474.HasModel 4 :=
  BitExclusion.not_order_474_4
spectrum_assert not_order_474_4 complete

theorem not_order_1286_5 : ¬ Law1286.HasModel 5 :=
  BitExclusion.not_order_1286_5
spectrum_assert not_order_1286_5 complete

end Spectrum
