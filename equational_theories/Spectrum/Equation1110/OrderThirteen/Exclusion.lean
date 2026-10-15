import equational_theories.Spectrum.Equation1110.OrderThirteen.OrdinaryCertificates
import equational_theories.Spectrum.Equation1110.RowNormalization
import equational_theories.Spectrum.Equation1110.OrderThirteenIdempotent
import equational_theories.Spectrum.Equation1110.OrderThirteen.Certificates.C2
import equational_theories.Spectrum.Equation1110.OrderThirteen.Certificates.C4

/-! No thirteen-element E1110 magma. Mathlib's permutation conjugacy theorem
reduces squaring to a canonical cycle type. Two-cycles are algebraically
impossible. A second relabelling fixes the support of squaring and
normalizes row zero, before checking compact refutations. -/
namespace Spectrum.E1110.OrderThirteen
open SmallOrders CycleRepresentatives

private theorem no_case2 (f : Fin 13 → Fin 13 → Fin 13)
    (h : Holds .e1110 f) (hD : ∀ x, f x x = data13 2 x) : False := by
  obtain ⟨g,hg,dg,hc⟩ := RowNormalization.normalize_three_row (by decide)
    (representative13 2) (by decide) (by decide) f h hD
  have h0 : g 0 0 = 1 := (dg 0).trans (by decide)
  have hd : g 0 0 = 0 → ∀ x, g x x = x := by intro hz; rw [h0] at hz; contradiction
  exact ForwardEncoding.no_operation_rowChain (data13 2) Certificates.C2.unsat g hg hd hc dg

private theorem no_case4 (f : Fin 13 → Fin 13 → Fin 13)
    (h : Holds .e1110 f) (hD : ∀ x, f x x = data13 4 x) : False := by
  obtain ⟨g,hg,dg,hc⟩ := RowNormalization.normalize_four_row (by decide)
    (representative13 4) (by decide) (by decide) f h hD
  have h0 : g 0 0 = 1 := (dg 0).trans (by decide)
  have hd : g 0 0 = 0 → ∀ x, g x x = x := by intro hz; rw [h0] at hz; contradiction
  exact ForwardEncoding.no_operation_slack (data13 4) 2 Certificates.C4.unsat g hg hd hc dg

/-- Normalize the remaining labels while preserving the support of squaring. -/
private theorem no_supported (i : Fin 101) (k : ℕ) (hk : 3 ≤ k) (hn : k ≤ 13)
    (hzero : data13 i 0 = 1) (hfix : ∀ x, k ≤ x.val → data13 i x = x)
    (hu : (ForwardEncoding.slackNat (data13 i) (k-2)).Unsat)
    (f : Fin 13 → Fin 13 → Fin 13) (h : Holds .e1110 f)
    (hD : ∀ x, f x x = data13 i x) : False := by
  obtain ⟨g,hg,dg,hc⟩ := RowNormalization.normalize_supported_row k hk hn
    (representative13 i) hzero hfix f h hD
  have h0 : g 0 0 = 1 := (dg 0).trans hzero
  have hd : g 0 0 = 0 → ∀ x, g x x = x := by intro hz; rw [h0] at hz; contradiction
  exact ForwardEncoding.no_operation_slack (data13 i) (k-2) hu g hg hd hc dg

private theorem no_operation (f : Fin 13 → Fin 13 → Fin 13)
    (h : Holds .e1110 f) : False := by
  classical
  let d : Equiv.Perm (Fin 13) := Equiv.ofBijective (fun x => f x x) (square_bijective h rfl)
  obtain ⟨i,e,he⟩ := conjugate13 d
  let g (x y : Fin 13) := e (f (e.symm x) (e.symm y))
  have hg : Holds .e1110 g := holds_relabel h e
  have hD (x : Fin 13) : g x x = data13 i x := by
    have hh := Equiv.congr_fun he x
    change e (f (e.symm x) (e.symm x)) = data13 i x at hh
    exact hh
  have hd : g 0 0 = 0 → ∀ x, g x x = x := by
    intro hz x
    rw [hD] at hz ⊢
    exact zero_fixed_implies_identity13 i hz x
  fin_cases i
  · exact not_idempotent g hg (hd ((hD 0).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_case2 g hg hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_case4 g hg hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 6 5 (by decide) (by decide) (by decide) (by decide)
      Certificates.C6.unsat g hg hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 9 6 (by decide) (by decide) (by decide) (by decide)
      Certificates.C9.unsat g hg hD
  · exact no_supported 10 6 (by decide) (by decide) (by decide) (by decide)
      Certificates.C10.unsat g hg hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 13 7 (by decide) (by decide) (by decide) (by decide)
      Certificates.C13.unsat g hg hD
  · exact no_supported 14 7 (by decide) (by decide) (by decide) (by decide)
      Certificates.C14.unsat g hg hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact SquareEncoding.no_operation_fixed (data13 19) Certificates.C19.unsat g hg hd hD
  · exact no_supported 20 8 (by decide) (by decide) (by decide) (by decide)
      Certificates.C20.unsat g hg hD
  · exact no_supported 21 8 (by decide) (by decide) (by decide) (by decide)
      Certificates.C21.unsat g hg hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 26 9 (by decide) (by decide) (by decide) (by decide)
      Certificates.C26.unsat g hg hD
  · exact no_supported 27 9 (by decide) (by decide) (by decide) (by decide)
      Certificates.C27.unsat g hg hD
  · exact SquareEncoding.no_operation_fixed (data13 28) Certificates.C28.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 29) Certificates.C29.unsat g hg hd hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 37 10 (by decide) (by decide) (by decide) (by decide)
      Certificates.C37.unsat g hg hD
  · exact SquareEncoding.no_operation_fixed (data13 38) Certificates.C38.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 39) Certificates.C39.unsat g hg hd hD
  · exact no_supported 40 10 (by decide) (by decide) (by decide) (by decide)
      Certificates.C40.unsat g hg hD
  · exact SquareEncoding.no_operation_fixed (data13 41) Certificates.C41.unsat g hg hd hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact SquareEncoding.no_operation_fixed (data13 50) Certificates.C50.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 51) Certificates.C51.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 52) Certificates.C52.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 53) Certificates.C53.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 54) Certificates.C54.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 55) Certificates.C55.unsat g hg hd hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact no_supported 68 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C68.unsat g hg hD
  · exact SquareEncoding.no_operation_fixed (data13 69) Certificates.C69.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 70) Certificates.C70.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 71) Certificates.C71.unsat g hg hd hD
  · exact no_supported 72 12 (by decide) (by decide) (by decide) (by decide)
      Certificates.C72.unsat g hg hD
  · exact SquareEncoding.no_operation_fixed (data13 73) Certificates.C73.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 74) Certificates.C74.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 75) Certificates.C75.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 76) Certificates.C76.unsat g hg hd hD
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 13) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact SquareEncoding.no_operation_fixed (data13 91) Certificates.C91.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 92) Certificates.C92.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 93) Certificates.C93.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 94) Certificates.C94.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 95) Certificates.C95.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 96) Certificates.C96.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 97) Certificates.C97.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 98) Certificates.C98.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 99) Certificates.C99.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data13 100) Certificates.C100.unsat g hg hd hD

end Spectrum.E1110.OrderThirteen

namespace Spectrum

theorem not_order_1110_13 : ¬ Law1110.HasModel 13 := by
  rintro ⟨M,hM⟩
  exact E1110.OrderThirteen.no_operation M.op ((SmallOrders.holds_iff .e1110 M).mpr hM)

spectrum_assert not_order_1110_13 complete
end Spectrum
