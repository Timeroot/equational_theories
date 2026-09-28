import equational_theories.Spectrum.Equation883Nine.Exclusion

/-! E883 has no nine-element model. Canonicalization covers all first-row
permutations; the 66 nonidentity representatives have checked LRAT refutations. -/

namespace Spectrum

theorem not_order_883_9 : ¬ Law883.HasModel 9 := E883Nine.not_order_883_9
spectrum_assert not_order_883_9 complete

end Spectrum
