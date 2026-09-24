import equational_theories.Spectrum.Equation63.Construction
import equational_theories.Spectrum.Shapes

/-! Explicit arithmetic induction: a finite interval, together with TD(8,q)
for q coprime to 30, covers every order at least 159. -/
namespace Spectrum.E63
open Law Law.MagmaLaw

theorem coprime_in_six (a : ℕ) : ∃ d : Fin 6, (a+d.val).Coprime 60 := by
  have h : ∀ r : Fin 60, ∃ d : Fin 6, (r.val+d.val).Coprime 60 := by decide +kernel
  obtain ⟨d, hd⟩ := h ⟨a%60, Nat.mod_lt _ (by decide)⟩
  refine ⟨d, ?_⟩
  change Nat.gcd (a+d.val) 60 = 1
  change Nat.gcd (a%60+d.val) 60 = 1 at hd
  rw [Nat.gcd_comm, Nat.gcd_rec] at hd ⊢
  simpa only [Nat.add_mod, Nat.mod_mod] using hd

/-- Only the finite interval 159 ≤ n < 1608 is needed for the cofinite tail. -/
theorem cofinite_induction
    (base : ∀ n, 159 ≤ n → n < 1608 → Law63.HasModel n) :
    ∀ n, 159 ≤ n → Law63.HasModel n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hs : n < 1608
    · exact base n hn hs
    · let a := (n+7)/8
      obtain ⟨d, hd⟩ := coprime_in_six a
      let q := a+d.val
      let r := n-7*q
      have hdlt := d.isLt
      have hq : 159 ≤ q := by dsimp [q, a]; omega
      have hr : 159 ≤ r := by dsimp [r, q, a]; omega
      have hrq : r ≤ q := by dsimp [r, q, a]; omega
      have hqn : q < n := by dsimp [q, a]; omega
      have hrn : r < n := by dsimp [r]; omega
      have he : 7*q+r=n := by dsimp [r, q, a]; omega
      rw [← he]
      exact seven (by omega) hd hrq (ih q hqn hq) (ih r hrn hr)

end Spectrum.E63
