import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourRow0
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourRow1
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourRow2
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourRow3
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourRow4
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourSquareOne
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourHead01
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourHead02
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourHead11
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourHead12
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.InsideFourCoverage
import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadPatterns

namespace Spectrum.E1483.OrderTwelve.InsideFourExclusion
open Std.Sat InsideFourRows RowsData
lemma representatives_unsat (j : Fin 5) : (rowFormula (row (representative j))).Unsat := by
  fin_cases j
  · exact Certificates.InsideFourRow0.unsat
  · exact Certificates.InsideFourRow1.unsat
  · exact Certificates.InsideFourRow2.unsat
  · exact Certificates.InsideFourRow3.unsat
  · exact Certificates.InsideFourRow4.unsat

lemma no_zero_head (f : A → A → A) (h : NormalForm f 4 true)
    (h0 : f 0 0 = 0) (h2 : f 0 2 = 0) (h3 : f 0 3 = 0) : False :=
  InsideFourRows.no_zero_head representatives_unsat Certificates.InsideFourCoverage.unsat f h h0 h2 h3

lemma no_model (f : A → A → A) (h : NormalForm f 4 true) : False := by
  have exclude (cells : List Encoding.Cell) (hn : (HeadLexEncoding.toNat 4 true cells).Unsat)
      (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False :=
    HeadLexEncoding.no_model 4 true cells hn f h.bounds.2 h.core h.sorted
      (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex hc
  have hs : f 0 0 = 0 ∨ f 0 0 = 1 := by simpa using h.core.first
  rcases hs with h0 | h1
  · have hh := HeadPatterns.insideFour f h.core h0 (h.predecessor h0) h.headLex
    simp only [HeadPatterns.insideFourHeads, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hh
    rcases hh with ⟨h2,h3⟩ | ⟨h2,h3⟩ | ⟨h2,h3⟩ | ⟨h2,h3⟩ | ⟨h2,h3⟩
    · exact no_zero_head f h h0 h2 h3
    · apply exclude _ Certificates.InsideFourHead01.unsat
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    · apply exclude _ Certificates.InsideFourHead02.unsat
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    · apply exclude _ Certificates.InsideFourHead11.unsat
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    · apply exclude _ Certificates.InsideFourHead12.unsat
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl <;> assumption
  · apply exclude _ Certificates.InsideFourSquareOne.unsat
    intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    exact h1

spectrum_assert no_model complete
end Spectrum.E1483.OrderTwelve.InsideFourExclusion
