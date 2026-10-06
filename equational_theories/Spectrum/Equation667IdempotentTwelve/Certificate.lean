import equational_theories.Spectrum.Equation667IdempotentTwelve.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/-! A compact refutation of the idempotent twelve-point cubic isotope.
The solver output is checked with Lean's proved LRAT checker; it is not
accepted merely because the external solver reported UNSAT. -/

namespace Spectrum.E667.IdempotentTwelve
open Std.Sat Std.Tactic.BVDecide LRAT

private def proof : Array IntAction :=
  (parseLRATProof (include_gzip_str
    "../../../data/spectrum/667_idempotent_twelve.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checked : check proof (natFormula 12) = true := by native_decide

theorem unsat : (natFormula 12).Unsat := check_sound proof _ checked

theorem not_idempotent [Magma (Fin 12)] (h : Equation667 (Fin 12)) :
    ¬ ∀ x : Fin 12, x ◇ x = x := no_idempotent_e667 unsat h

spectrum_assert not_idempotent complete
end Spectrum.E667.IdempotentTwelve

namespace Spectrum.E667
/-- The idempotent subclass is empty at order twelve. -/
theorem not_idempotent_twelve {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hc : Nat.card A = 12) : ¬ ∀ x : A, x ◇ x = x := by
  classical
  intro hi
  let e : A ≃ Fin 12 := Finite.equivFinOfCardEq hc
  letI : Magma (Fin 12) := ⟨fun x y => e (e.symm x ◇ e.symm y)⟩
  apply IdempotentTwelve.not_idempotent (fun x y => ?_) (fun x => ?_)
  · change x = e (e.symm y ◇ e.symm (e (e.symm x ◇
      e.symm (e (e.symm (e (e.symm x ◇ e.symm x)) ◇ e.symm y)))))
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
      congrArg e (h (e.symm x) (e.symm y))
  · change e (e.symm x ◇ e.symm x) = x
    simp only [hi, Equiv.apply_symm_apply]

spectrum_assert not_idempotent_twelve complete
end Spectrum.E667
