import equational_theories.Spectrum.SmallOrders.Encoding

/-! The idempotent branch of the E1110 order-thirteen search. -/
set_option maxHeartbeats 0
set_option maxRecDepth 65536

namespace Spectrum.E1110.OrderThirteen
open Std.Sat SmallOrders
open SmallOrders.Encoding (Atom p meaning code code_injective)
open E63.OrderTen.Encoding (sat_single sanitize)

variable {n : ℕ} [NeZero n]

def formula (n : ℕ) [NeZero n] : CNF (Atom n) := Encoding.formula .e1110 n ++ ⟨#[[(p 0 0 0,true)]]⟩
def natFormula (n : ℕ) [NeZero n] : CNF ℕ := sanitize ((formula n).relabel code)

theorem no_normalized_of_unsat (hn : (natFormula n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hi : ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : False := by
  have hf : (formula n).Sat (meaning .e1110 f) := by
    apply E63.OrderTen.Encoding.sat_append
    · exact Encoding.model_formula .e1110 f h (fun _ => hi) hc
    · apply sat_single
      simp [CNF.Clause.eval, meaning, p, hi]
  have unsat_raw : ((formula n).relabel code).Unsat := by
    intro a
    cases he : (((formula n).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula n).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hn' (meaning .e1110 f)
  rw [hf] at hh
  contradiction

theorem not_idempotent_of_unsat (hn : (natFormula n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f) : ¬ ∀ x, f x x = x := by
  intro hi
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let g (x y : Fin n) := e (f (e.symm x) (e.symm y))
  apply no_normalized_of_unsat hn g (holds_relabel h e)
  · intro x
    simp [g, hi]
  · intro y
    simpa only [g, he'] using hc y

end Spectrum.E1110.OrderThirteen
