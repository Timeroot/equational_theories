import equational_theories.Spectrum.Equation667RightIdentityTwelve.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/-! The saved refutation is replayed with Lean's proved LRAT checker.
The ordinary build never invokes an external model finder. -/
namespace Spectrum.E667.RightIdentityTwelve
open Std.Sat Std.Tactic.BVDecide LRAT

private def proof : Array IntAction :=
  (parseLRATProof (include_gzip_str
    "../../../data/spectrum/667_right_identity_twelve.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checked : check proof (natFormula 12) = true := by native_decide

theorem unsat : (natFormula 12).Unsat := check_sound proof _ checked

end Spectrum.E667.RightIdentityTwelve

namespace Spectrum.E667
/-- No twelve-element E667 magma has a right identity. -/
theorem not_right_identity_twelve {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hc : Nat.card A = 12) (u : A) : ¬ ∀ x : A, x ◇ u = x := by
  classical
  intro hu
  let e : A ≃ Fin 12 := Finite.equivFinOfCardEq hc
  let f (x y : Fin 12) := e (e.symm x ◇ e.symm y)
  apply RightIdentityTwelve.no_right_identity RightIdentityTwelve.unsat (by decide) f
    (fun x y => ?_) (e u) (fun x => ?_)
  · dsimp only [f]
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
      congrArg e (h (e.symm x) (e.symm y)).symm
  · simp only [f, Equiv.symm_apply_apply, hu, Equiv.apply_symm_apply]

spectrum_assert not_right_identity_twelve complete
end Spectrum.E667
