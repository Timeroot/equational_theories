import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C0
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C4
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C6
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C10
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C14
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C20
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C21
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C28
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C29
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C39
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C40
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C41
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C53
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C54
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C55
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C72
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C73
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C74
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C75
import equational_theories.Spectrum.Equation467.OrderTwelve.Certificates.C76
import equational_theories.Spectrum.Equation467.OrderTwelve.Normalization

/-! Complete order-twelve exclusion: classify squaring by its cycle type,
remove forbidden two- and three-cycles algebraically, then use compact checked
refutations for the twenty remaining types. -/
namespace Spectrum.E467.OrderTwelve
open FixedEncoding E1110.CycleRepresentatives

private theorem no_two (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (d : Fin 12 → Fin 12) (hd : ∀ x, f x x = d x) (x : Fin 12)
    (hp : d (d x) = x) (hn : d x ≠ x) : False := by
  have hp' : square f (square f x) = x := by simpa only [square,hd] using hp
  exact hn (by simpa only [square,hd] using square_period_two f h x hp')

private theorem no_three (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (d : Fin 12 → Fin 12) (hd : ∀ x, f x x = d x) (x : Fin 12)
    (hp : d (d (d x)) = x) (hn : d x ≠ x) : False := by
  have hp' : square f (square f (square f x)) = x := by simpa only [square,hd] using hp
  exact hn (by simpa only [square,hd] using square_period_three f h x hp')

private theorem no_supported (i : Fin 77) (k : ℕ) (hk : 4 ≤ k) (hn : k ≤ 12)
    (hz : representative12 i 0 = 1)
    (hf : ∀ x : Fin 12, k ≤ x.val → representative12 i x = x)
    (hu : (FixedEncoding.natFormula (representative12 i) (k-2)).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hd : ∀ x, f x x = data12 i x) : False := by
  obtain ⟨g,hg,dg,hc⟩ := normalize_supported_row k hk hn (representative12 i) hz hf f h hd
  exact FixedEncoding.impossible_of_unsat _ _ g hg dg hc hu

private theorem no_operation (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) : False := by
  classical
  let d : Equiv.Perm (Fin 12) := Equiv.ofBijective (square f)
    ⟨square_injective f h, Finite.surjective_of_injective (square_injective f h)⟩
  obtain ⟨i,e,he⟩ := conjugate12 d
  let g := relabel f e
  have hg : Holds g := holds_relabel f h e
  have hd (x : Fin 12) : g x x = data12 i x := by
    have hh := Equiv.congr_fun he x
    change e (f (e.symm x) (e.symm x)) = data12 i x at hh
    exact hh
  fin_cases i
  · have hi : ∀ x : Fin 12, data12 0 x = x := by decide
    obtain ⟨q,hq,dq,hc⟩ := normalize_idempotent g hg (fun x => (hd x).trans (hi x))
    exact FixedEncoding.impossible_of_unsat _ 1 q hq
      (fun x => (dq x).trans (hi x).symm) hc Certificates.C0.unsat
  · exact no_two g hg (data12 1) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 2) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 3) hd 0 (by decide) (by decide)
  · exact no_supported 4 4 (by decide) (by decide) (by decide) (by decide)
      Certificates.C4.unsat g hg hd
  · exact no_two g hg (data12 5) hd 0 (by decide) (by decide)
  · exact no_supported 6 5 (by decide) (by decide) (by decide) (by decide)
      Certificates.C6.unsat g hg hd
  · exact no_two g hg (data12 7) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 8) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 9) hd 0 (by decide) (by decide)
  · exact no_supported 10 6 (by decide) (by decide) (by decide) (by decide)
      Certificates.C10.unsat g hg hd
  · exact no_two g hg (data12 11) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 12) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 13) hd 0 (by decide) (by decide)
  · exact no_supported 14 7 (by decide) (by decide) (by decide) (by decide)
      Certificates.C14.unsat g hg hd
  · exact no_two g hg (data12 15) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 16) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 17) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 18) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 19) hd 0 (by decide) (by decide)
  · exact no_supported 20 8 (by decide) (by decide) (by decide) (by decide)
      Certificates.C20.unsat g hg hd
  · exact no_supported 21 8 (by decide) (by decide) (by decide) (by decide)
      Certificates.C21.unsat g hg hd
  · exact no_two g hg (data12 22) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 23) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 24) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 25) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 26) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 27) hd 0 (by decide) (by decide)
  · exact no_supported 28 9 (by decide) (by decide) (by decide) (by decide)
      Certificates.C28.unsat g hg hd
  · exact no_supported 29 9 (by decide) (by decide) (by decide) (by decide)
      Certificates.C29.unsat g hg hd
  · exact no_two g hg (data12 30) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 31) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 32) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 33) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 34) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 35) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 36) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 37) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 38) hd 0 (by decide) (by decide)
  · exact no_supported 39 10 (by decide) (by decide) (by decide) (by decide)
      Certificates.C39.unsat g hg hd
  · exact no_supported 40 10 (by decide) (by decide) (by decide) (by decide)
      Certificates.C40.unsat g hg hd
  · exact no_supported 41 10 (by decide) (by decide) (by decide) (by decide)
      Certificates.C41.unsat g hg hd
  · exact no_two g hg (data12 42) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 43) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 44) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 45) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 46) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 47) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 48) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 49) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 50) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 51) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 52) hd 0 (by decide) (by decide)
  · exact no_supported 53 11 (by decide) (by decide) (by decide) (by decide)
      Certificates.C53.unsat g hg hd
  · exact no_supported 54 11 (by decide) (by decide) (by decide) (by decide)
      Certificates.C54.unsat g hg hd
  · exact no_supported 55 11 (by decide) (by decide) (by decide) (by decide)
      Certificates.C55.unsat g hg hd
  · exact no_two g hg (data12 56) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 57) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 58) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 59) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 60) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 61) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 62) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 63) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 64) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 65) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 66) hd 0 (by decide) (by decide)
  · exact no_two g hg (data12 67) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 68) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 69) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 70) hd 0 (by decide) (by decide)
  · exact no_three g hg (data12 71) hd 0 (by decide) (by decide)
  · exact no_supported 72 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C72.unsat g hg hd
  · exact no_supported 73 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C73.unsat g hg hd
  · exact no_supported 74 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C74.unsat g hg hd
  · exact no_supported 75 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C75.unsat g hg hd
  · exact no_supported 76 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C76.unsat g hg hd

end Spectrum.E467.OrderTwelve
namespace Spectrum

theorem not_order_467_12 : ¬ Law467.HasModel 12 := by
  rintro ⟨M,hM⟩
  exact E467.OrderTwelve.no_operation M.op ((@Law467.models_iff _ M).mp hM)

spectrum_assert not_order_467_12 complete
end Spectrum
