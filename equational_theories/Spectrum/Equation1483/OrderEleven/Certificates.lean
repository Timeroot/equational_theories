import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank2Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank3Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank4Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank4Inside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank5Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank5Inside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank6Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank6Inside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank7Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank7Inside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank8Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank8Inside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank9Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank9Inside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank10Outside
import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates.Rank10Inside

/-! The sixteen cases of the simultaneous-image normalization. -/
namespace Spectrum.E1483.OrderEleven
open Magma.Central1483.CNF

private lemma outside_of_small_rank (f : Fin 11 → Fin 11 → Fin 11)
    (k : Nat) (zero : Bool) (hk : k ≤ 3) (h : RankCore f k zero) : zero = false := by
  cases zero
  · rfl
  · have hpos : 0 < k := by
      have hz := (h.imageZero (f 0 0)).mp ⟨0,rfl⟩
      change (f 0 0).val < k at hz
      omega
    obtain ⟨z,hz⟩ := (h.imageZero 0).mpr (by simpa using hpos)
    have hb := h.rowRank 0 z
    rw [hz,h.rankZero] at hb
    nlinarith

theorem no_operation (f : Fin 11 → Fin 11 → Fin 11)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) : False := by
  obtain ⟨k,zero,g,⟨hk0,hk1⟩,hg,hs,ht⟩ := Normalization.exists_normalized f h
  interval_cases k
  · have hz := outside_of_small_rank g 2 zero (by omega) hg
    subst zero
    exact ImageEncoding.no_small_model 2 false Certificates.Rank2Outside.unsat g hg hs ht
  · have hz := outside_of_small_rank g 3 zero (by omega) hg
    subst zero
    exact ImageEncoding.no_small_model 3 false Certificates.Rank3Outside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 4 false Certificates.Rank4Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 4 true Certificates.Rank4Inside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 5 false Certificates.Rank5Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 5 true Certificates.Rank5Inside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 6 false Certificates.Rank6Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 6 true Certificates.Rank6Inside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 7 false Certificates.Rank7Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 7 true Certificates.Rank7Inside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 8 false Certificates.Rank8Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 8 true Certificates.Rank8Inside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 9 false Certificates.Rank9Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 9 true Certificates.Rank9Inside.unsat g hg hs ht
  · cases zero
    · exact ImageEncoding.no_small_model 10 false Certificates.Rank10Outside.unsat g hg hs ht
    · exact ImageEncoding.no_small_model 10 true Certificates.Rank10Inside.unsat g hg hs ht

spectrum_assert no_operation complete
end Spectrum.E1483.OrderEleven
