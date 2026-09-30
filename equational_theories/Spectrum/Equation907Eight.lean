import equational_theories.Spectrum.Equation907Eight.Exclusion

/-! E907 has no eight-element model. Lean checks all 8! first-row permutations
and the LRAT refutations of all 45 canonical forms, including the identity.
Only left cancellation, a consequence of the law and finiteness, is used. -/
namespace Spectrum

theorem not_order_907_8 : ¬ Law907.HasModel 8 := E907Eight.not_order_907_8
spectrum_assert not_order_907_8 complete

end Spectrum
