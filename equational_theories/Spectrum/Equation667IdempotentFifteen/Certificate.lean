import equational_theories.Spectrum.Equation667IdempotentFifteen.Encoding
import equational_theories.Definability.IncludeGzip

/-! Thirteen short refutations, following a separately verified row reduction.
The external solver is never run by an ordinary Lean build. -/
namespace Spectrum.E667.IdempotentFifteen
open Std.Sat Std.Tactic.BVDecide LRAT
private def proofs : Fin 13 → Array IntAction :=
  ![(parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/0.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/1.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/2.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/3.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/4.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/5.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/6.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/7.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/8.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/9.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/10.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/11.lrat.gz").toUTF8).toOption.getD #[],
    (parseLRATProof (include_gzip_str "../../../data/spectrum/667_idempotent_fifteen_lrat/12.lrat.gz").toUTF8).toOption.getD #[]]

@[spectrum_native]
theorem checked : ∀ i : Fin 13, check (proofs i) (natFormula i) = true := by native_decide

theorem unsat (i : Fin 13) : (natFormula i).Unsat := check_sound (proofs i) _ (checked i)

theorem not_idempotent [Magma (Fin 15)] (h : Equation667 (Fin 15)) :
    ¬ ∀ x : Fin 15, x ◇ x = x := by
  intro hi
  let d (x y : Fin 15) := y ◇ (y ◇ x)
  have hd (x y : Fin 15) : x ◇ d x y = y := by
    simpa only [d,hi] using (h y x).symm
  have cubic : E63.OrderTen.Cubic d := by
    intro x y
    change x ◇ (x ◇ d x (d x y)) = y
    rw [hd,hd]
  exact no_cubic_model unsat d cubic (fun x => by simp only [d,hi])
end Spectrum.E667.IdempotentFifteen

namespace Spectrum.E667
/-- There is no globally idempotent fifteen-element E667 model. -/
theorem not_idempotent_fifteen {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hc : Nat.card A = 15) : ¬ ∀ x : A, x ◇ x = x := by
  classical
  intro hi
  let e : A ≃ Fin 15 := Finite.equivFinOfCardEq hc
  letI : Magma (Fin 15) := ⟨fun x y => e (e.symm x ◇ e.symm y)⟩
  apply IdempotentFifteen.not_idempotent (fun x y => ?_) (fun x => ?_)
  · change x = e (e.symm y ◇ e.symm (e (e.symm x ◇
      e.symm (e (e.symm (e (e.symm x ◇ e.symm x)) ◇ e.symm y)))))
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
      congrArg e (h (e.symm x) (e.symm y))
  · change e (e.symm x ◇ e.symm x) = x
    simp only [hi,Equiv.apply_symm_apply]

spectrum_assert not_idempotent_fifteen complete
end Spectrum.E667
