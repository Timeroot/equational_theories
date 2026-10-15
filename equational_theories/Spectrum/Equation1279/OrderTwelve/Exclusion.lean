import equational_theories.Spectrum.Equation1279.OrderTwelve.Certificates

/-! The square permutation has one of 77 cycle types. Two-cycles are excluded
algebraically; the other 35 types have small, independently checked refutations. -/
namespace Spectrum.E1279.OrderTwelve
open SmallOrders E1110.CycleRepresentatives

private theorem identity_diagonal : ∀ x : Fin 12, data12 0 x = x := by decide

private theorem no_idempotent (f : Fin 12 → Fin 12 → Fin 12)
    (h : Holds .e1279 f) (hi : ∀ x, f x x = x) : False := by
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let g (x y : Fin 12) := e (f (e.symm x) (e.symm y))
  have hg : Holds .e1279 g := holds_relabel h e
  have hgi : ∀ x, g x x = data12 0 x := by
    intro x
    simpa [g,hi] using (identity_diagonal x).symm
  have hgc : ∀ y, (g 0 y).val ≤ y.val + 1 := by intro y; simpa only [g,he'] using hc y
  exact DirectEncoding.no_operation (data12 0) 1 (unsat 0) g hg hgi hgc

private theorem no_supported (j : Fin 35)
    (hk : 2 ≤ allowance j + 1) (hn : allowance j + 1 ≤ 12)
    (hzero : data12 (sourceIndex j) 0 = 1)
    (hfix : ∀ x, allowance j + 1 ≤ x.val → data12 (sourceIndex j) x = x)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1279 f)
    (hD : ∀ x, f x x = data12 (sourceIndex j) x) : False := by
  obtain ⟨g,hg,dg,hc⟩ := normalize_supported_row (allowance j + 1) hk hn
    (representative12 (sourceIndex j)) hzero hfix f h hD
  exact DirectEncoding.no_operation (data12 (sourceIndex j)) (allowance j) (unsat j)
    g hg dg (by simpa using hc)

private theorem no_operation (f : Fin 12 → Fin 12 → Fin 12)
    (h : Holds .e1279 f) : False := by
  classical
  let d : Equiv.Perm (Fin 12) := Equiv.ofBijective (fun x => f x x) (square_bijective h rfl)
  obtain ⟨i,e,he⟩ := conjugate12 d
  let g (x y : Fin 12) := e (f (e.symm x) (e.symm y))
  have hg : Holds .e1279 g := holds_relabel h e
  have hD (x : Fin 12) : g x x = data12 i x := by
    have hh := Equiv.congr_fun he x
    change e (f (e.symm x) (e.symm x)) = data12 i x at hh
    exact hh
  fin_cases i
  · exact no_idempotent g hg (fun x => (hD x).trans (identity_diagonal x))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 1 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 2 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 3 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 4 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 5 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 6 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 7 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 8 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 9 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 10 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 11 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 12 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 13 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 14 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 15 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 16 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 17 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 18 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 19 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 20 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 21 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 22 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 23 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 24 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 25 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 26 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 27 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 28 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 29 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 30 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 31 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 32 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 33 (by decide) (by decide) (by decide) (by decide) g hg hD
  · exact no_supported 34 (by decide) (by decide) (by decide) (by decide) g hg hD

end Spectrum.E1279.OrderTwelve
namespace Spectrum

theorem not_order_1279_12 : ¬ Law1279.HasModel 12 := by
  rintro ⟨M,hM⟩
  exact E1279.OrderTwelve.no_operation M.op ((SmallOrders.holds_iff .e1279 M).mpr hM)

spectrum_assert not_order_1279_12 complete
end Spectrum
