import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank5OutsideShort
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank5OutsideBack1
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank5OutsideBack2
import equational_theories.Spectrum.Equation1483.OrderTwelve.Certificates.Rank5OutsideBack3

/-! Four small branches replace one long rank-five replay. The first-row chain
bound gives `0*1 ∈ {1,2}` and `0*2 ∈ {1,2,3}`. Only the `0*1=2` branch needs
the second split. Its last branch also uses the proved second-row symmetry. -/
namespace Spectrum.E1483.OrderTwelve.RankFiveOutside
open Std.Sat
abbrev A := Fin 12

private lemma head_no_model (cells : List Encoding.Cell)
    (hn : (HeadLexEncoding.toNat 5 false cells).Unsat)
    (f : A → A → A) (h : NormalForm f 5 false)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False :=
  HeadLexEncoding.no_model 5 false cells hn f h.bounds.2 h.core h.sorted
    (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex hc

lemma no_model (f : A → A → A) (h : NormalForm f 5 false) : False := by
  obtain ⟨g,hg,hrow,hl⟩ := SecondLexNormalization.refine_normalForm f 5 false h
  have hpos (i : A) : 0 < (g 0 i).val := by
    have hh := (hg.core.imageZero (g 0 i)).mp ⟨i,rfl⟩
    exact hh.1
  have h1 : g 0 1 = 1 ∨ g 0 1 = 2 := by
    have hc := hg.chain 1
    have hp := hpos 1
    have hv : (g 0 1).val = 1 ∨ (g 0 1).val = 2 := by
      change (g 0 1).val ≤ 2 at hc
      omega
    rcases hv with hv|hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases h1 with h1|h1
  · exact head_no_model [(0,1,1)] Certificates.Rank5OutsideShort.unsat g hg (by
      intro c hc
      simp only [List.mem_singleton] at hc
      subst c
      exact h1)
  · have h2 : g 0 2 = 1 ∨ g 0 2 = 2 ∨ g 0 2 = 3 := by
      have hc := hg.chain 2
      have hp := hpos 2
      have hv : (g 0 2).val = 1 ∨ (g 0 2).val = 2 ∨ (g 0 2).val = 3 := by
        change (g 0 2).val ≤ 3 at hc
        omega
      rcases hv with hv|hv|hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Or.inl (Fin.ext hv))
      · exact Or.inr (Or.inr (Fin.ext hv))
    rcases h2 with h2|h2|h2
    · exact head_no_model [(0,1,2),(0,2,1)] Certificates.Rank5OutsideBack1.unsat g hg (by
        intro c hc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl|rfl <;> assumption)
    · exact head_no_model [(0,1,2),(0,2,2)] Certificates.Rank5OutsideBack2.unsat g hg (by
        intro c hc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl|rfl <;> assumption)
    · exact SecondLexEncoding.no_model false 5 false [(0,1,2),(0,2,3)]
        Certificates.Rank5OutsideBack3.unsat g hg hl (by
          intro c hc
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl <;> assumption)

end Spectrum.E1483.OrderTwelve.RankFiveOutside
