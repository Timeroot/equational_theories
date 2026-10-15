import equational_theories.Spectrum.Equation1486.OrderTen.Certificates.RankTwoInside
import equational_theories.Spectrum.Equation1486.OrderTen.Certificates.RankTwoOutsideSmall
import equational_theories.Spectrum.Equation1486.OrderTen.Certificates.NoIdemInside
import equational_theories.Spectrum.Equation1486.OrderTen.Certificates.NoIdemOutside
import equational_theories.Spectrum.Equation1486.OrderTen.Certificates.Idempotent

/-! Five exhaustive cases, obtained from the square-row rank bound and
proved relabeling arguments, exclude a ten-element E1486 magma. -/
namespace Spectrum
open E1486.OrderTen E1486.SquareRows

theorem not_order_1486_10 : ¬ Law1486.HasModel 10 := by
  rintro ⟨M,hM⟩
  have h : Lawful M.op := fun x y z => ((@Law1486.models_iff _ M).mp hM x y z).symm
  by_cases ht : ∃ a, (row M.op a).card = 2
  · obtain ⟨g,inside,hg,hr⟩ := normalize_two M.op h ht
    cases inside with
    | false =>
      exact Encoding.no_model_of_unsat _ Certificates.RankTwoOutsideSmall.unsat g
        (Encoding.model_small g hg false hr)
    | true =>
      exact Encoding.no_model_of_unsat _ Certificates.RankTwoInside.unsat g
        (Encoding.model_small g hg true hr)
  · have h3 := three_of_no_two M.op h (fun a ha => ht ⟨a,ha⟩)
    by_cases hi : ∃ a, M.op a a = a
    · obtain ⟨g,hg,hr3,hr0,hgi,hr1,hr2⟩ := normalize_three_idem M.op h h3 hi
      exact Encoding.no_model_of_unsat _ Certificates.Idempotent.unsat g
        (Encoding.model_idem g hg hr0 hr3 hgi hr1 hr2)
    · push Not at hi
      obtain ⟨g,inside,hg,hr3,hr0,hs,hgi,h01,h10⟩ := normalize_three_noidem M.op h h3 hi
      cases inside with
      | false =>
        exact Encoding.no_model_of_unsat _ Certificates.NoIdemOutside.unsat g
          (Encoding.model_noIdem g hg false hr0 hr3 hs hgi h01 h10)
      | true =>
        exact Encoding.no_model_of_unsat _ Certificates.NoIdemInside.unsat g
          (Encoding.model_noIdem g hg true hr0 hr3 hs hgi h01 h10)

spectrum_assert not_order_1486_10 complete
end Spectrum
