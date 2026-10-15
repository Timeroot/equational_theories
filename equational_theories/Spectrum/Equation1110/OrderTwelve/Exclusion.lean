import equational_theories.Spectrum.Equation1110.RowNormalization
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C0
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C2
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C4
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C6
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C9
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C10
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C13
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C14
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C19
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C20
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C21
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C26
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C27
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C28
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C29
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C37
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C38
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C39
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C40
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C41
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C50
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C51
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C52
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C53
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C54
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C55
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C68
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C69
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C70
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C71
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C72
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C73
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C74
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C75
import equational_theories.Spectrum.Equation1110.OrderTwelve.Certificates.C76

/-! No twelve-element E1110 magma. Squaring is a permutation; Mathlib conjugacy
reduces it to a canonical cycle type. A two-cycle contradicts E1110 by two
cancellations. The remaining cases have independently checked certificates. -/
namespace Spectrum.E1110.OrderTwelve
open SmallOrders CycleRepresentatives

private theorem no_operation (f : Fin 12 → Fin 12 → Fin 12)
    (h : Holds .e1110 f) : False := by
  classical
  let d : Equiv.Perm (Fin 12) := Equiv.ofBijective (fun x => f x x)
    (square_bijective h rfl)
  obtain ⟨i,e,he⟩ := conjugate12 d
  let g (x y : Fin 12) := e (f (e.symm x) (e.symm y))
  have hg : Holds .e1110 g := holds_relabel h e
  have hD (x : Fin 12) : g x x = data12 i x := by
    have hh := Equiv.congr_fun he x
    change e (f (e.symm x) (e.symm x)) = data12 i x at hh
    exact hh
  have hd : g 0 0 = 0 → ∀ x, g x x = x := by
    intro hz x
    rw [hD] at hz ⊢
    exact zero_fixed_implies_identity12 i hz x
  fin_cases i
  · have hid : ∀ x : Fin 12, data12 0 x = x := by decide
    exact OrderThirteen.not_idempotent_of_unsat Certificates.C0.unsat g hg
      (fun x => (hD x).trans (hid x))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · obtain ⟨q, hq, hqD, hqc⟩ := RowNormalization.normalize_three_row
      (by decide : 3 ≤ 12) (representative12 2) (by decide) (by decide) g hg hD
    have hq0 : q 0 0 ≠ 0 := by rw [hqD]; decide
    exact ForwardEncoding.no_operation_rowChain (data12 2) Certificates.C2.unsat
      q hq (fun h0 => (hq0 h0).elim) hqc hqD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · obtain ⟨q, hq, hqD, hqc⟩ := RowNormalization.normalize_four_row
      (by decide : 4 ≤ 12) (representative12 4) (by decide) (by decide) g hg hD
    have hq0 : q 0 0 ≠ 0 := by rw [hqD]; decide
    exact ForwardEncoding.no_operation_slack (data12 4) 2 Certificates.C4.unsat
      q hq (fun h0 => (hq0 h0).elim) hqc hqD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · obtain ⟨q, hq, hqD, hqc⟩ := RowNormalization.normalize_supported_row
      5 (by decide) (by decide : 5 ≤ 12) (representative12 6)
      (by decide) (by decide) g hg hD
    have hq0 : q 0 0 ≠ 0 := by rw [hqD]; decide
    exact ForwardEncoding.no_operation_slack (data12 6) 3 Certificates.C6.unsat
      q hq (fun h0 => (hq0 h0).elim) hqc hqD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · obtain ⟨q, hq, hqD, hqc⟩ := RowNormalization.normalize_supported_row
      6 (by decide) (by decide : 6 ≤ 12) (representative12 9)
      (by decide) (by decide) g hg hD
    have hq0 : q 0 0 ≠ 0 := by rw [hqD]; decide
    exact ForwardEncoding.no_operation_slack (data12 9) 4 Certificates.C9.unsat
      q hq (fun h0 => (hq0 h0).elim) hqc hqD
  · exact SquareEncoding.no_operation_fixed (data12 10) Certificates.C10.unsat g hg hd hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact SquareEncoding.no_operation_fixed (data12 13) Certificates.C13.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 14) Certificates.C14.unsat g hg hd hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact SquareEncoding.no_operation_fixed (data12 19) Certificates.C19.unsat g hg hd hD
  · obtain ⟨q, hq, hqD, hqc⟩ := RowNormalization.normalize_supported_row
      8 (by decide) (by decide : 8 ≤ 12) (representative12 20)
      (by decide) (by decide) g hg hD
    have hq0 : q 0 0 ≠ 0 := by rw [hqD]; decide
    exact ForwardEncoding.no_operation_slack (data12 20) 6 Certificates.C20.unsat
      q hq (fun h0 => (hq0 h0).elim) hqc hqD
  · exact SquareEncoding.no_operation_fixed (data12 21) Certificates.C21.unsat g hg hd hD
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact (by decide : (0 : Fin 12) ≠ 1)
      (square_two_cycle hg ((hD 0).trans (by decide)) ((hD 1).trans (by decide)))
  · exact SquareEncoding.no_operation_fixed (data12 26) Certificates.C26.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 27) Certificates.C27.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 28) Certificates.C28.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 29) Certificates.C29.unsat g hg hd hD
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
  · exact SquareEncoding.no_operation_fixed (data12 37) Certificates.C37.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 38) Certificates.C38.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 39) Certificates.C39.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 40) Certificates.C40.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 41) Certificates.C41.unsat g hg hd hD
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
  · exact SquareEncoding.no_operation_fixed (data12 50) Certificates.C50.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 51) Certificates.C51.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 52) Certificates.C52.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 53) Certificates.C53.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 54) Certificates.C54.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 55) Certificates.C55.unsat g hg hd hD
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
  · exact SquareEncoding.no_operation_fixed (data12 68) Certificates.C68.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 69) Certificates.C69.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 70) Certificates.C70.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 71) Certificates.C71.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 72) Certificates.C72.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 73) Certificates.C73.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 74) Certificates.C74.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 75) Certificates.C75.unsat g hg hd hD
  · exact SquareEncoding.no_operation_fixed (data12 76) Certificates.C76.unsat g hg hd hD

end Spectrum.E1110.OrderTwelve

namespace Spectrum

theorem not_order_1110_12 : ¬ Law1110.HasModel 12 := by
  rintro ⟨M,hM⟩
  exact E1110.OrderTwelve.no_operation M.op ((SmallOrders.holds_iff .e1110 M).mpr hM)

spectrum_assert not_order_1110_12 complete
end Spectrum
