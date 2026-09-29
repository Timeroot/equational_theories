import equational_theories.Spectrum.Equation1083_1286.CommonPointWitnesses
import equational_theories.Spectrum.Equation1083_1286.BinarySeed
import equational_theories.Spectrum.Equation1083_1286.PrimeSeeds
import equational_theories.Spectrum.Shapes

/-! Named, proved families used by the spectrum catalogue. -/
namespace Spectrum
open Law Law.MagmaLaw

def designPairOrders : Set ℕ := {n | ∃ t : ℕ, n = 1008*1009^(t+1)+11}
def commonPointSquareOrders : Set ℕ := {n | ∃ t : ℕ, n = 119*(30*t+2)^2-6}
def commonPointFourthOrders : Set ℕ := {n | ∃ t : ℕ, n = 119*(30*t+2)^4-6}
def binaryPointFourthOrders : Set ℕ := {n | ∃ t : ℕ, n = 224*(30*t+1)^4-6}

namespace E1083E1286

theorem design_pair_lower {which : Bool} : designPairOrders ⊆ (law which).spectrum := by
  rintro n ⟨t,rfl⟩
  exact ⟨by omega, exponential_family t⟩

theorem common_square_lower : commonPointSquareOrders ⊆ Law1083.spectrum := by
  rintro n ⟨t,rfl⟩
  have hp : 1 ≤ (30*t+2)^2 := Nat.one_le_pow _ _ (by omega)
  exact ⟨by omega, quadratic_family t⟩

theorem common_fourth_lower : commonPointFourthOrders ⊆ Law1286.spectrum := by
  rintro n ⟨t,rfl⟩
  have hp : 1 ≤ (30*t+2)^4 := Nat.one_le_pow _ _ (by omega)
  exact ⟨by omega, quartic_family t⟩

theorem binary_fourth_lower : binaryPointFourthOrders ⊆ Law1286.spectrum := by
  rintro n ⟨t,rfl⟩
  have hp : 1 ≤ (30*t+1)^4 := Nat.one_le_pow _ _ (by omega)
  exact ⟨by omega, BinarySeed.quartic_family t⟩

theorem family1083 : squares ∪ commonPointSquareOrders ∪ designPairOrders ⊆ Law1083.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · rintro n ⟨hn,k,rfl⟩
      have hk : k ≠ 0 := by rintro rfl; simp at hn
      letI : NeZero k := ⟨hk⟩
      exact ⟨hn, QuadraticSeeds.square1083 k⟩
    · exact common_square_lower
  · exact design_pair_lower (which := false)

theorem family1286 : fourthPowers ∪ commonPointFourthOrders ∪ binaryPointFourthOrders ∪
    designPairOrders ⊆ Law1286.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · apply Set.union_subset
      · rintro n ⟨hn,k,rfl⟩
        have hk : k ≠ 0 := by rintro rfl; simp at hn
        letI : NeZero k := ⟨hk⟩
        exact ⟨hn, (quartic (which := true) k).hasModel⟩
      · exact common_fourth_lower
    · exact binary_fourth_lower
  · exact design_pair_lower (which := true)

spectrum_assert family1083 complete
spectrum_assert family1286 complete

end E1083E1286
end Spectrum
