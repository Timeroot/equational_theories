import equational_theories.Spectrum.Equation63.IdempotentArithmetic
import equational_theories.Spectrum.Equation63.Induction

/-! An explicit constructive cofinite bound for idempotent E63 models.
The finite basis covers 1480 ≤ n < 12176; seven-group gluing then supplies
every larger order. No general asymptotic design-existence theorem is used. -/
set_option maxRecDepth 65536
namespace Spectrum.E63

private theorem idempotent_base {n : ℕ} (hn : 1480 ≤ n) (hs : n < 12176) :
    Model (Fin n) true := by
  by_cases hsmall : n < 2086
  · apply IdempotentFiniteBasis.model hsmall
    intro he
    have := IdempotentFiniteBasis.exceptions_lt n he
    omega
  · obtain ⟨q, r, hq, hc, hrq, hqs, hrs, hqe, hre, he⟩ :=
      IdempotentArithmetic.decomposition ⟨n,hs⟩ (Nat.le_of_not_gt hsmall)
    change 7*q+r = n at he
    rw [← he]
    exact seven_idempotent hq hc hrq
      (IdempotentFiniteBasis.model hqs hqe)
      (IdempotentFiniteBasis.model hrs hre)

/-- Every order at least 1480 supports an idempotent E63 model. -/
theorem idempotent_all_large {n : ℕ} (hn : 1480 ≤ n) : Model (Fin n) true := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n < 12176
    · exact idempotent_base hn hs
    · let a := (n+7)/8
      obtain ⟨d, hd⟩ := coprime_in_six a
      let q := a+d.val
      let r := n-7*q
      have hdlt := d.isLt
      have hq : 1480 ≤ q := by dsimp [q, a]; omega
      have hr : 1480 ≤ r := by dsimp [r, q, a]; omega
      have hrq : r ≤ q := by dsimp [r, q, a]; omega
      have hqn : q < n := by dsimp [q, a]; omega
      have hrn : r < n := by dsimp [r]; omega
      have he : 7*q+r=n := by dsimp [r, q, a]; omega
      rw [← he]
      exact seven_idempotent (by omega) hd hrq (ih q hqn hq) (ih r hrn hr)

/-- The finite list of possible exceptions controls all orders, including the
constructible small orders. Membership in the list does not assert exclusion. -/
theorem idempotent_model_of_not_exception {n : ℕ}
    (he : n ∉ IdempotentFiniteBasis.exceptions) : Model (Fin n) true := by
  by_cases hs : n < 2086
  · exact IdempotentFiniteBasis.model hs he
  · exact idempotent_all_large (by omega)

end Spectrum.E63
