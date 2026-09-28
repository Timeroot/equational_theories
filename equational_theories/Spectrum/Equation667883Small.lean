import equational_theories.Spectrum.Equation667883Small.Six667
import equational_theories.Spectrum.Equation667883Small.Six883

/-!+# Six-element exclusions for E667 and E883

The two refutations cover all six-element magma tables.  The finite
quasigroup consequences in the accompanying `Basic` module are independent
of these finite certificates; the certificates need no cancellation or
normalization assumptions.
-/

namespace Spectrum

theorem not_order_667_6 : ¬ Law667.HasModel 6 := E667883.not_order_667_6
spectrum_assert not_order_667_6 complete

theorem not_order_883_6 : ¬ Law883.HasModel 6 := E667883.not_order_883_6
spectrum_assert not_order_883_6 complete

end Spectrum
