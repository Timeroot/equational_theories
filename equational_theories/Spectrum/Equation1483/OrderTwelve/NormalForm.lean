import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadLexNormalization
import equational_theories.Spectrum.Equation1483.OrderTwelve.RowOneNormalization

/-! The two lexicographic refinements can be combined: the second changes no
entry of the first row, so all restrictions already proved for that row survive. -/
namespace Spectrum.E1483.OrderTwelve
open CNF Normalization RowOneNormalization HeadLexNormalization
abbrev A := Fin 12

structure NormalForm (f : A → A → A) (k : Nat) (zero : Bool) : Prop where
  bounds : 2 ≤ k ∧ k < 12
  core : RankCore f k zero
  sorted : Sorted f k zero
  chain : ∀ y, (f 0 y).val ≤ y.val+1
  predecessor : f 0 0 = 0 → f 0 1 = 0
  headLex : HeadLex f k zero
  firstMention : FirstMention f k zero

lemma exists_normalForm (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A, NormalForm g k zero := by
  obtain ⟨k,zero,g,hk,hg,hs,hchain,hI,hlex⟩ := HeadLexNormalization.exists_normalized f h
  obtain ⟨g',hg',hs',hrow,hm⟩ := RowOneNormalization.refine_model g k zero hg hs hk.1
  refine ⟨k,zero,g',hk,hg',hs',?_,?_,?_,hm⟩
  · intro y
    rw [hrow y]
    exact hchain y
  · intro hz
    rw [hrow 1]
    exact hI ((hrow 0).symm.trans hz)
  · exact HeadLexNormalization.head_congr g g' k zero hlex (fun i _ => hrow i)

end Spectrum.E1483.OrderTwelve
