import equational_theories.Spectrum.Equation667IdempotentTwelve.Encoding
import SpectrumCertificateData
import SpectrumCertificateData.Replay
import equational_theories.Spectrum.Status

/-! A compact refutation of the idempotent thirteen-point cubic isotope.
The solver output is checked with Lean's proved LRAT checker; it is not
accepted merely because the external solver reported UNSAT. -/

namespace Spectrum.E667.IdempotentThirteen
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
open IdempotentTwelve

private def proof : Array IntAction :=
  CompactRup.reconstruct (include_binary_gzip
    "../../data/spectrum/667_idempotent_thirteen.rup.gz") (natFormula 13)

@[spectrum_native]
theorem checked : check proof (natFormula 13) = true := by native_decide

theorem unsat : (natFormula 13).Unsat := check_sound proof _ checked

theorem not_idempotent [Magma (Fin 13)] (h : Equation667 (Fin 13)) :
    ¬ ∀ x : Fin 13, x ◇ x = x := no_idempotent_e667 unsat h

spectrum_assert not_idempotent complete
end Spectrum.E667.IdempotentThirteen

namespace Spectrum.E667
/-- The idempotent subclass is empty at order thirteen. -/
theorem not_idempotent_thirteen {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hc : Nat.card A = 13) : ¬ ∀ x : A, x ◇ x = x := by
  classical
  intro hi
  let e : A ≃ Fin 13 := Finite.equivFinOfCardEq hc
  letI : Magma (Fin 13) := ⟨fun x y => e (e.symm x ◇ e.symm y)⟩
  apply IdempotentThirteen.not_idempotent (fun x y => ?_) (fun x => ?_)
  · change x = e (e.symm y ◇ e.symm (e (e.symm x ◇
      e.symm (e (e.symm (e (e.symm x ◇ e.symm x)) ◇ e.symm y)))))
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
      congrArg e (h (e.symm x) (e.symm y))
  · change e (e.symm x ◇ e.symm x) = x
    simp only [hi, Equiv.apply_symm_apply]

spectrum_assert not_idempotent_thirteen complete
end Spectrum.E667
