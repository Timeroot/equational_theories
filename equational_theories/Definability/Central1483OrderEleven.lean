import equational_theories.Definability.Central1483Normalization
import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import equational_theories.Definability.Generated.Central1483Rank2Zero0
import equational_theories.Definability.Generated.Central1483Rank3Zero0
import equational_theories.Definability.Generated.Central1483Rank4Zero0
import equational_theories.Definability.Generated.Central1483Rank4Zero1
import equational_theories.Definability.Generated.Central1483Rank5Zero0
import equational_theories.Definability.Generated.Central1483Rank5Zero1
import equational_theories.Definability.Generated.Central1483Rank6Zero0
import equational_theories.Definability.Generated.Central1483Rank6Zero1
import equational_theories.Definability.Generated.Central1483Rank7Zero0
import equational_theories.Definability.Generated.Central1483Rank7Zero1
import equational_theories.Definability.Generated.Central1483Rank8Zero0
import equational_theories.Definability.Generated.Central1483Rank8Zero1
import equational_theories.Definability.Generated.Central1483Rank9Zero0
import equational_theories.Definability.Generated.Central1483Rank9Zero1
import equational_theories.Definability.Generated.Central1483Rank10Zero0
import equational_theories.Definability.Generated.Central1483Rank10Zero1

/-!
# E1483 has no model of order eleven

Any hypothetical model can be relabeled so that a row of minimum rank is row
zero, its image is an initial segment (possibly omitting zero), and its tail is
sorted. Ordinary proofs establish every condition of the resulting finite SAT
instance. Sixteen explicit LRAT certificates refute all possible rank cases.
-/

namespace Magma.Central1483
open Refutation

theorem no_operation_eleven (f : Fin 11 → Fin 11 → Fin 11)
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
  · cases zero
    · exact CNF.no_rank_of_unsat 10 false unsatRank10Zero0 g hg
    · exact CNF.no_rank_of_unsat 10 true unsatRank10Zero1 g hg

end Magma.Central1483

namespace Spectrum

theorem not_order_1483_11 : ¬ Law1483.HasModel 11 := by
  rintro ⟨M, hM⟩
  have h := (@Law1483.models_iff (Fin 11) M).mp hM
  exact Magma.Central1483.no_operation_eleven M.op (fun x y z => (h x y z).symm)

/-- info: 'Spectrum.not_order_1483_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Magma.Central1483.Refutation.checkRank10Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank10Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank2Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank3Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank4Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank4Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank5Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank5Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank6Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank6Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank7Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank7Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank8Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank8Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank9Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank9Zero1._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms not_order_1483_11

end Spectrum
