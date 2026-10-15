import equational_theories.Spectrum.Equation1483.OrderTwelve.NormalForm
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP011P021
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP011P022
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP011P023
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P021
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P031P041
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P031P042
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P031P043
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P031P044
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P032P041
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P032P042
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P032P043
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P032P044
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P033P041
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P033P042
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P033P043
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P033P044
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P022P034
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P031
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P032P041
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P032P042
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P032P043
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P032P044
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P033P041
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P033P042
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P033P043
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P033P044
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P034P041
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P034P042
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P034P043
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank4OutsideP012P023P034P044

/-! A short adaptive partition of the first-row image head. Each branch uses
a separately checked certificate; the small natural-number splits are proved below. -/
namespace Spectrum.E1483.OrderTwelve.OutsideFourExclusion
open CNF Normalization

theorem no_model (f : A → A → A) (h : NormalForm f 4 false) : False := by
  have hp (i : A) : 1 ≤ (f 0 i).val := by
    have hv : 0 < (f 0 i).val ∧ (f 0 i).val ≤ 4 :=
      (h.core.imageZero _).mp ⟨i,rfl⟩
    omega
  have hb (i : A) : (f 0 i).val ≤ 4 := output_bound f 4 false h.core i
  have hv1 : (f 0 1).val = 1 ∨ (f 0 1).val = 2 := by
    have hp1 := hp 1; have hb1 := hb 1; have hc1 := h.chain 1
    norm_num at hc1
    omega
  rcases hv1 with hv1|hv1
  · have he1 : f 0 1 = 1 := Fin.ext (by simpa using hv1)
    have hv2 : (f 0 2).val = 1 ∨ (f 0 2).val = 2 ∨ (f 0 2).val = 3 := by
      have hp2 := hp 2; have hb2 := hb 2; have hc2 := h.chain 2
      norm_num at hc2
      omega
    rcases hv2 with hv2|hv2|hv2
    · have he2 : f 0 2 = 1 := Fin.ext (by simpa using hv2)
      apply HeadLexEncoding.no_model 4 false [(0,1,1), (0,2,1)] Certificates.Rank4OutsideP011P021.unsat
        f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> assumption
    · have he2 : f 0 2 = 2 := Fin.ext (by simpa using hv2)
      apply HeadLexEncoding.no_model 4 false [(0,1,1), (0,2,2)] Certificates.Rank4OutsideP011P022.unsat
        f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> assumption
    · have he2 : f 0 2 = 3 := Fin.ext (by simpa using hv2)
      apply HeadLexEncoding.no_model 4 false [(0,1,1), (0,2,3)] Certificates.Rank4OutsideP011P023.unsat
        f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> assumption
  · have he1 : f 0 1 = 2 := Fin.ext (by simpa using hv1)
    have hv2 : (f 0 2).val = 1 ∨ (f 0 2).val = 2 ∨ (f 0 2).val = 3 := by
      have hp2 := hp 2; have hb2 := hb 2; have hc2 := h.chain 2
      norm_num at hc2
      omega
    rcases hv2 with hv2|hv2|hv2
    · have he2 : f 0 2 = 1 := Fin.ext (by simpa using hv2)
      apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,1)] Certificates.Rank4OutsideP012P021.unsat
        f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
      intro c hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> assumption
    · have he2 : f 0 2 = 2 := Fin.ext (by simpa using hv2)
      have hv3 : (f 0 3).val = 1 ∨ (f 0 3).val = 2 ∨ (f 0 3).val = 3 ∨ (f 0 3).val = 4 := by
        have hp3 := hp 3; have hb3 := hb 3; have hc3 := h.chain 3
        norm_num at hc3
        omega
      rcases hv3 with hv3|hv3|hv3|hv3
      · have he3 : f 0 3 = 1 := Fin.ext (by simpa using hv3)
        have hv4 : (f 0 4).val = 1 ∨ (f 0 4).val = 2 ∨ (f 0 4).val = 3 ∨ (f 0 4).val = 4 := by
          have hp4 := hp 4; have hb4 := hb 4; have hc4 := h.chain 4
          norm_num at hc4
          omega
        rcases hv4 with hv4|hv4|hv4|hv4
        · have he4 : f 0 4 = 1 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,1), (0,4,1)] Certificates.Rank4OutsideP012P022P031P041.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 2 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,1), (0,4,2)] Certificates.Rank4OutsideP012P022P031P042.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 3 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,1), (0,4,3)] Certificates.Rank4OutsideP012P022P031P043.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 4 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,1), (0,4,4)] Certificates.Rank4OutsideP012P022P031P044.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
      · have he3 : f 0 3 = 2 := Fin.ext (by simpa using hv3)
        have hv4 : (f 0 4).val = 1 ∨ (f 0 4).val = 2 ∨ (f 0 4).val = 3 ∨ (f 0 4).val = 4 := by
          have hp4 := hp 4; have hb4 := hb 4; have hc4 := h.chain 4
          norm_num at hc4
          omega
        rcases hv4 with hv4|hv4|hv4|hv4
        · have he4 : f 0 4 = 1 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,2), (0,4,1)] Certificates.Rank4OutsideP012P022P032P041.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 2 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,2), (0,4,2)] Certificates.Rank4OutsideP012P022P032P042.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 3 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,2), (0,4,3)] Certificates.Rank4OutsideP012P022P032P043.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 4 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,2), (0,4,4)] Certificates.Rank4OutsideP012P022P032P044.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
      · have he3 : f 0 3 = 3 := Fin.ext (by simpa using hv3)
        have hv4 : (f 0 4).val = 1 ∨ (f 0 4).val = 2 ∨ (f 0 4).val = 3 ∨ (f 0 4).val = 4 := by
          have hp4 := hp 4; have hb4 := hb 4; have hc4 := h.chain 4
          norm_num at hc4
          omega
        rcases hv4 with hv4|hv4|hv4|hv4
        · have he4 : f 0 4 = 1 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,3), (0,4,1)] Certificates.Rank4OutsideP012P022P033P041.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 2 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,3), (0,4,2)] Certificates.Rank4OutsideP012P022P033P042.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 3 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,3), (0,4,3)] Certificates.Rank4OutsideP012P022P033P043.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 4 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,3), (0,4,4)] Certificates.Rank4OutsideP012P022P033P044.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
      · have he3 : f 0 3 = 4 := Fin.ext (by simpa using hv3)
        apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,2), (0,3,4)] Certificates.Rank4OutsideP012P022P034.unsat
          f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
        intro c hc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl|rfl|rfl <;> assumption
    · have he2 : f 0 2 = 3 := Fin.ext (by simpa using hv2)
      have hv3 : (f 0 3).val = 1 ∨ (f 0 3).val = 2 ∨ (f 0 3).val = 3 ∨ (f 0 3).val = 4 := by
        have hp3 := hp 3; have hb3 := hb 3; have hc3 := h.chain 3
        norm_num at hc3
        omega
      rcases hv3 with hv3|hv3|hv3|hv3
      · have he3 : f 0 3 = 1 := Fin.ext (by simpa using hv3)
        apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,1)] Certificates.Rank4OutsideP012P023P031.unsat
          f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
        intro c hc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl|rfl|rfl <;> assumption
      · have he3 : f 0 3 = 2 := Fin.ext (by simpa using hv3)
        have hv4 : (f 0 4).val = 1 ∨ (f 0 4).val = 2 ∨ (f 0 4).val = 3 ∨ (f 0 4).val = 4 := by
          have hp4 := hp 4; have hb4 := hb 4; have hc4 := h.chain 4
          norm_num at hc4
          omega
        rcases hv4 with hv4|hv4|hv4|hv4
        · have he4 : f 0 4 = 1 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,2), (0,4,1)] Certificates.Rank4OutsideP012P023P032P041.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 2 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,2), (0,4,2)] Certificates.Rank4OutsideP012P023P032P042.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 3 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,2), (0,4,3)] Certificates.Rank4OutsideP012P023P032P043.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 4 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,2), (0,4,4)] Certificates.Rank4OutsideP012P023P032P044.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
      · have he3 : f 0 3 = 3 := Fin.ext (by simpa using hv3)
        have hv4 : (f 0 4).val = 1 ∨ (f 0 4).val = 2 ∨ (f 0 4).val = 3 ∨ (f 0 4).val = 4 := by
          have hp4 := hp 4; have hb4 := hb 4; have hc4 := h.chain 4
          norm_num at hc4
          omega
        rcases hv4 with hv4|hv4|hv4|hv4
        · have he4 : f 0 4 = 1 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,3), (0,4,1)] Certificates.Rank4OutsideP012P023P033P041.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 2 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,3), (0,4,2)] Certificates.Rank4OutsideP012P023P033P042.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 3 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,3), (0,4,3)] Certificates.Rank4OutsideP012P023P033P043.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 4 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,3), (0,4,4)] Certificates.Rank4OutsideP012P023P033P044.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
      · have he3 : f 0 3 = 4 := Fin.ext (by simpa using hv3)
        have hv4 : (f 0 4).val = 1 ∨ (f 0 4).val = 2 ∨ (f 0 4).val = 3 ∨ (f 0 4).val = 4 := by
          have hp4 := hp 4; have hb4 := hb 4; have hc4 := h.chain 4
          norm_num at hc4
          omega
        rcases hv4 with hv4|hv4|hv4|hv4
        · have he4 : f 0 4 = 1 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,4), (0,4,1)] Certificates.Rank4OutsideP012P023P034P041.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 2 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,4), (0,4,2)] Certificates.Rank4OutsideP012P023P034P042.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 3 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,4), (0,4,3)] Certificates.Rank4OutsideP012P023P034P043.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption
        · have he4 : f 0 4 = 4 := Fin.ext (by simpa using hv4)
          apply HeadLexEncoding.no_model 4 false [(0,1,2), (0,2,3), (0,3,4), (0,4,4)] Certificates.Rank4OutsideP012P023P034P044.unsat
            f h.bounds.2 h.core h.sorted (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl <;> assumption

spectrum_assert no_model complete
end Spectrum.E1483.OrderTwelve.OutsideFourExclusion
