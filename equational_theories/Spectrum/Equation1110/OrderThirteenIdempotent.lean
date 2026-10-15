import equational_theories.Spectrum.Equation1110.OrderThirteenEncoding
import equational_theories.Spectrum.Equation1110.Commutative
import equational_theories.Spectrum.Status
import SpectrumCertificateData
import SpectrumCertificateData.Replay

/-! A compact certificate excludes the idempotent (hence also commutative)
branch at order thirteen. It does not exclude general E1110 magmas. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Spectrum.E1110.OrderThirteen
open Std.Sat Std.Tactic.BVDecide LRAT

private def proof : Array IntAction := Spectrum.CertificateData.CompactRup.reconstruct
  (include_binary_xz "../../../data/spectrum/1110_order13_rup/idempotent.rup.xz") (natFormula 13)

@[spectrum_native]
theorem idempotent_checked : check proof (natFormula 13) = true := by native_decide

theorem idempotent_unsat : (natFormula 13).Unsat := check_sound proof _ idempotent_checked

theorem not_idempotent (f : Fin 13 → Fin 13 → Fin 13)
    (h : SmallOrders.Holds .e1110 f) : ¬ ∀ x, f x x = x :=
  not_idempotent_of_unsat idempotent_unsat f h

end Spectrum.E1110.OrderThirteen
