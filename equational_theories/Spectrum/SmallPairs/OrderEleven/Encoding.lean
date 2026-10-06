import equational_theories.Spectrum.SmallPairs.OrderEleven.Rows
import equational_theories.Spectrum.SmallPairs.Encoding

namespace Spectrum.SmallPairs.OrderEleven
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open Encoding (Atom p meaning code code_injective)

def rowUnits (r : Fin 11 → Fin 11) : CNF (Atom 11) :=
  all1 fun y => ⟨#[[(p 0 y (r y), true)]]⟩

def formula (r : Fin 11 → Fin 11) : CNF (Atom 11) :=
  Encoding.formula .e1313 11 ++ rowUnits r

def natFormula (r : Fin 11 → Fin 11) : CNF ℕ :=
  sanitize ((formula r).relabel code)

theorem model_formula (f : Fin 11 → Fin 11 → Fin 11) (h : Holds .e1313 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    (formula (f 0)).Sat (meaning .e1313 f) := by
  apply sat_append
  · exact Encoding.model_formula .e1313 f h hd hc
  · apply sat_all1; intro y
    apply sat_single
    simp [CNF.Clause.eval, meaning, p]

theorem no_model_of_unsat (f : Fin 11 → Fin 11 → Fin 11) (h : Holds .e1313 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hn : (natFormula (f 0)).Unsat) : False := by
  have unsat_raw : ((formula (f 0)).relabel code).Unsat := by
    intro a
    cases he : (((formula (f 0)).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula (f 0)).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hn' (meaning .e1313 f)
  rw [model_formula f h hd hc] at hh
  contradiction

end Spectrum.SmallPairs.OrderEleven
