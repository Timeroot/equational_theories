import equational_theories.Spectrum.Equation667FixedSquare.Certificates
import equational_theories.Spectrum.Equation667Twelve.Certificates

/-! The exhaustive order-twelve exclusion. Bijective squaring is covered by
77 permutation types. Noninjective squaring has three collision patterns;
the idempotent pattern reduces to 50 first-row types. Every finite refutation
is replayed by Lean's verified LRAT checker. -/
namespace Spectrum.E667.Twelve
open RightIdentityTwelve (Holds)
open Spectrum.FiniteSearch

theorem no_model_fin (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) : False := by
  letI : Magma (Fin 12) := ⟨f⟩
  rcases (square_cases (Q := Fin 12)) with hi | hid | hthree | hfour
  · exact FixedSquare.not_injective_square f h hi
  · obtain ⟨e,x,hxe,hee,hxx⟩ := hid
    let t := Equiv.swap e (0 : Fin 12)
    have ht : t e = 0 := Equiv.swap_apply_left _ _
    have hts : t.symm 0 = e := by
      apply t.injective
      rw [Equiv.apply_symm_apply,ht]
    let g := relabel f t
    have hg : Holds g := RightIdentityTwelve.holds_relabel h t
    have hg0 : g 0 0 = 0 := by
      change t (f (t.symm 0) (t.symm 0)) = 0
      rw [hts]
      exact (congrArg t hee).trans ht
    have hgx : g (t x) (t x) = 0 := by
      change t (f (t.symm (t x)) (t.symm (t x))) = 0
      simp only [Equiv.symm_apply_apply]
      exact (congrArg t hxx).trans ht
    have hx0 : t x ≠ 0 := fun he => hxe (t.injective (he.trans ht.symm))
    exact no_idempotent_collision g hg hg0 (t x) hx0 hgx
  · obtain ⟨a,b,c,hab,hac,hbc,ha,hb,hc⟩ := hthree
    exact no_three three_refuted f h a b c hab hac hbc ha hb hc
  · obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,ha,hb,hc⟩ := hfour
    exact no_four four_refuted f h a b c d hab hac had hbc hbd hcd ha hb hc

spectrum_assert no_model_fin complete
end Spectrum.E667.Twelve

namespace Spectrum

theorem not_order_667_12 : ¬ Law667.HasModel 12 := by
  rintro ⟨M,hM⟩
  exact E667.Twelve.no_model_fin M.op
    (fun x y => (((@Law667.models_iff _ M).mp hM) x y).symm)

spectrum_assert not_order_667_12 complete
end Spectrum
