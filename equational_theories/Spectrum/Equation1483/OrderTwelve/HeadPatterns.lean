import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadLexNormalization

/-! Five possible normalized heads of an idempotent rank-four row. Its third
iterate is constant; swapping labels two and three removes duplicate shapes.
This lemma applies only when the distinguished element is idempotent. -/
namespace Spectrum.E1483.OrderTwelve.HeadPatterns
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization HeadLexNormalization
abbrev A := Fin 12

def insideFourHeads : List (A × A) := [(0,0),(0,1),(0,2),(1,1),(1,2)]

lemma insideFour (f : A → A → A) (h : RankCore f 4 true)
    (h0 : f 0 0 = 0) (h1 : f 0 1 = 0) (hl : HeadLex f 4 true) :
    (f 0 2, f 0 3) ∈ insideFourHeads := by
  have hb2 := output_bound f 4 true h (2 : A)
  have hb3 := output_bound f 4 true h (3 : A)
  norm_num [bound] at hb2 hb3
  have ht (x : A) : f 0 (f 0 (f 0 x)) = 0 := by
    simpa only [h0] using h.source 0 0 x
  have hl2 : f 0 2 ≤ Equiv.swap (2 : A) 3 (f 0 3) := by
    have he := hl 2 3 2 (by decide) (by decide) (by decide) (by decide)
    have hp (j : A) (hj : j < 2) : f 0 j = swapRow f 2 3 j := by
      have hh : j.val < 2 := hj
      interval_cases hv : j.val
      · have hj0 : j = 0 := Fin.ext hv
        subst j
        simp [swapRow,Equiv.swap_apply_def,h0]
      · have hj1 : j = 1 := Fin.ext hv
        subst j
        simp [swapRow,Equiv.swap_apply_def,h1]
    simpa [swapRow] using he hp
  have ht2 := ht 2
  have ht3 := ht 3
  interval_cases hv2 : (f 0 2).val <;> interval_cases hv3 : (f 0 3).val
  all_goals
    have hf2 : f 0 2 = Fin.ofNat 12 (f 0 2).val := by simp
    have hf3 : f 0 3 = Fin.ofNat 12 (f 0 3).val := by simp
    rw [hv2] at hf2
    rw [hv3] at hf3
    simp only [show Fin.ofNat 12 0 = (0 : A) from rfl,
      show Fin.ofNat 12 1 = (1 : A) from rfl,
      show Fin.ofNat 12 2 = (2 : A) from rfl,
      show Fin.ofNat 12 3 = (3 : A) from rfl] at hf2 hf3
    simp_all [insideFourHeads, Equiv.swap_apply_def]

end Spectrum.E1483.OrderTwelve.HeadPatterns
