import equational_theories.Spectrum.Equation1516Quartic
import equational_theories.Spectrum.Equation63.ExtendedBounds
import equational_theories.Spectrum.DupontTwists

/-! The new order-sixteen construction fills the old final gap at 688,
as `688 = 16 * 43`, reducing the E1516 cofinite cutoff from 689 to 675. -/

namespace Spectrum.E1516

set_option maxRecDepth 4096

theorem model688 : Law1516.HasModel 688 :=
  model16.mul (DupontTwists.models
    (E63.FieldBounds.model (n := 43) (by decide +kernel))).2.2.2.2

private theorem bound : ∀ n ∈ E63.ExtendedBounds.remaining, n < 675 ∨ n = 688 :=
  by decide +kernel

theorem all_large {n : ℕ} (hn : 675 ≤ n) : Law1516.HasModel n := by
  by_cases h : n = 688
  · subst n
    exact model688
  · apply (DupontTwists.models (E63.ExtendedBounds.model ?_)).2.2.2.2
    intro he
    rcases bound n he with hlt | heq
    · omega
    · exact h heq

theorem cofinite : CofiniteSpectrum Law1516 :=
  ⟨675, fun _ hn => ⟨by omega, all_large hn⟩⟩

spectrum_assert model688 complete
spectrum_assert all_large complete
spectrum_assert cofinite complete

end Spectrum.E1516
