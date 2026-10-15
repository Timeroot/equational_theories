import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree
import equational_theories.Spectrum.Equation1483.OrderTwelve.InsideFourExclusion
import equational_theories.Spectrum.Equation1483.OrderTwelve.OutsideFourExclusion
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankFiveOutside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank2Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank5Inside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank6Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank6Inside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank7Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank7Inside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank8Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank8Inside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank9Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank9Inside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank10Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank10Inside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank11Outside
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank11Inside
import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status

/-! E1483 has no twelve-element model. The minimum translation rank gives a
finite partition. Lexicographic normalizations and short first-row partitions
keep each independently checked certificate small; all coverage is proved in Lean.
See docs/1483_order12.md for the constructions and measurements. -/
namespace Spectrum.E1483.OrderTwelve
open CNF

lemma outside_of_small_rank (f : A → A → A) (k : Nat) (zero : Bool)
    (hk : 2 ≤ k ∧ k ≤ 3) (h : RankCore f k zero) : zero = false := by
  cases zero
  · rfl
  · exfalso
    have hz : ∃ z, f 0 z = 0 := (h.imageZero 0).mpr (by
      change 0 < k
      omega)
    obtain ⟨z,hz⟩ := hz
    have hb := h.rowRank 0 z
    rw [hz,h.rankZero] at hb
    nlinarith

theorem no_operation (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) : False := by
  obtain ⟨k,zero,g,hg⟩ := exists_normalForm f h
  have hk0 := hg.bounds.1
  have hk1 := hg.bounds.2
  interval_cases k
  · have hz := outside_of_small_rank g 2 zero (by decide) hg.core
    subst zero
    exact RowOneEncoding.no_model 2 false [] Certificates.Rank2Outside.unsat
      g hg.core hg.sorted (by simpa using hg.chain 1) hg.firstMention (by simp)
  · have hz := outside_of_small_rank g 3 zero (by decide) hg.core
    subst zero
    obtain ⟨q,hq,_,hl⟩ := SecondLexNormalization.refine_normalForm g 3 false hg
    exact RankThree.no_model q hq hl
  · cases zero
    · exact OutsideFourExclusion.no_model g hg
    · exact InsideFourExclusion.no_model g hg
  · cases zero
    · exact RankFiveOutside.no_model g hg
    · exact HeadLexEncoding.no_model 5 true [] Certificates.Rank5Inside.unsat
        g hg.bounds.2 hg.core hg.sorted (by simpa using hg.chain 1)
        hg.firstMention hg.predecessor hg.headLex (by simp)
  · cases zero
    · exact HeadLexEncoding.no_model 6 false [] Certificates.Rank6Outside.unsat
        g hg.bounds.2 hg.core hg.sorted (by simpa using hg.chain 1)
        hg.firstMention hg.predecessor hg.headLex (by simp)
    · exact HeadLexEncoding.no_model 6 true [] Certificates.Rank6Inside.unsat
        g hg.bounds.2 hg.core hg.sorted (by simpa using hg.chain 1)
        hg.firstMention hg.predecessor hg.headLex (by simp)
  · cases zero
    · exact HeadLexEncoding.no_model 7 false [] Certificates.Rank7Outside.unsat
        g hg.bounds.2 hg.core hg.sorted (by simpa using hg.chain 1)
        hg.firstMention hg.predecessor hg.headLex (by simp)
    · exact HeadLexEncoding.no_model 7 true [] Certificates.Rank7Inside.unsat
        g hg.bounds.2 hg.core hg.sorted (by simpa using hg.chain 1)
        hg.firstMention hg.predecessor hg.headLex (by simp)
  · cases zero
    · exact ImageEncoding.no_fixed_model 8 false [] Certificates.Rank8Outside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
    · exact ImageEncoding.no_fixed_model 8 true [] Certificates.Rank8Inside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
  · cases zero
    · exact ImageEncoding.no_fixed_model 9 false [] Certificates.Rank9Outside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
    · exact ImageEncoding.no_fixed_model 9 true [] Certificates.Rank9Inside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
  · cases zero
    · exact ImageEncoding.no_fixed_model 10 false [] Certificates.Rank10Outside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
    · exact ImageEncoding.no_fixed_model 10 true [] Certificates.Rank10Inside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
  · cases zero
    · exact ImageEncoding.no_fixed_model 11 false [] Certificates.Rank11Outside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)
    · exact ImageEncoding.no_fixed_model 11 true [] Certificates.Rank11Inside.unsat
        g hg.core hg.sorted (by simpa using hg.chain 1) (by simp)

spectrum_assert no_operation complete
end Spectrum.E1483.OrderTwelve

namespace Spectrum

theorem not_order_1483_12 : ¬ Law1483.HasModel 12 := by
  rintro ⟨M,hM⟩
  have h := (@Law1483.models_iff (Fin 12) M).mp hM
  exact E1483.OrderTwelve.no_operation M.op (fun x y z => (h x y z).symm)

spectrum_assert not_order_1483_12 complete
end Spectrum
