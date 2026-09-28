import equational_theories.Spectrum.Equation1483.TenNormalization
import equational_theories.Spectrum.Equation1483.TenCases.Rank2Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank3Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank4Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank4Zero1
import equational_theories.Spectrum.Equation1483.TenCases.Rank5Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank5Zero1
import equational_theories.Spectrum.Equation1483.TenCases.Rank6Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank6Zero1
import equational_theories.Spectrum.Equation1483.TenCases.Rank7Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank7Zero1
import equational_theories.Spectrum.Equation1483.TenCases.Rank8Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank8Zero1
import equational_theories.Spectrum.Equation1483.TenCases.Rank9Zero0
import equational_theories.Spectrum.Equation1483.TenCases.Rank9Zero1
import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status

namespace Spectrum.E1483.OrderTen
open Refutation

theorem no_operation (f : Fin 10 → Fin 10 → Fin 10)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) : False := by
  obtain ⟨k, zero, g, ⟨hk0, hk1⟩, hg⟩ := Normalized.exists_normalized f h
  interval_cases k
  · have hz := Normalized.small_rank_zero_false g 2 zero (by omega) hg
    subst zero
    exact CNF.no_rank_of_unsat 2 false unsatRank2Zero0 g hg
  · have hz := Normalized.small_rank_zero_false g 3 zero (by omega) hg
    subst zero
    exact CNF.no_rank_of_unsat 3 false unsatRank3Zero0 g hg
  · cases zero
    · exact CNF.no_rank_of_unsat 4 false unsatRank4Zero0 g hg
    · exact CNF.no_rank_of_unsat 4 true unsatRank4Zero1 g hg
  · cases zero
    · exact CNF.no_rank_of_unsat 5 false unsatRank5Zero0 g hg
    · exact CNF.no_rank_of_unsat 5 true unsatRank5Zero1 g hg
  · cases zero
    · exact CNF.no_rank_of_unsat 6 false unsatRank6Zero0 g hg
    · exact CNF.no_rank_of_unsat 6 true unsatRank6Zero1 g hg
  · cases zero
    · exact CNF.no_rank_of_unsat 7 false unsatRank7Zero0 g hg
    · exact CNF.no_rank_of_unsat 7 true unsatRank7Zero1 g hg
  · cases zero
    · exact CNF.no_rank_of_unsat 8 false unsatRank8Zero0 g hg
    · exact CNF.no_rank_of_unsat 8 true unsatRank8Zero1 g hg
  · cases zero
    · exact CNF.no_rank_of_unsat 9 false unsatRank9Zero0 g hg
    · exact CNF.no_rank_of_unsat 9 true unsatRank9Zero1 g hg

end Spectrum.E1483.OrderTen

namespace Spectrum

theorem not_order_1483_10 : ¬ Law1483.HasModel 10 := by
  rintro ⟨M, hM⟩
  have h := (@Law1483.models_iff (Fin 10) M).mp hM
  exact E1483.OrderTen.no_operation M.op (fun x y z => (h x y z).symm)

spectrum_assert not_order_1483_10 complete

end Spectrum
