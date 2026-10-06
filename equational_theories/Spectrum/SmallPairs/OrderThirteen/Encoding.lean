import equational_theories.Spectrum.SmallPairs.OrderThirteen.Reduction
import equational_theories.Spectrum.SmallPairs.Encoding

namespace Spectrum.SmallPairs.OrderThirteen
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open Encoding (Atom p q meaning code code_injective)

/-- The converse cancellation steps in the two triangles of the encoding.
These are redundant logically, but save substantial certificate search. -/
def cancellation : CNF (Atom 13) := all1 fun x => all1 fun y =>
  all1 fun a => all1 fun b =>
  ⟨#[[(p x x a,true), (p a y b,false), (q x y b,false)],
     [(q x y a,true), (p a y b,false), (p y b x,false)]]⟩

theorem model_cancellation (f : Fin 13 → Fin 13 → Fin 13) (h : Holds .e1279 f) :
    cancellation.Sat (meaning .e1279 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  have hab (hb : f a y = b) (hq : middle .e1279 f x y = b) : f x x = a := by
    apply (right_bijective h (Or.inr rfl) y).1
    exact hq.trans hb.symm
  have hbc (hb : f a y = b) (hc : f y b = x) : middle .e1279 f x y = a := by
    apply (right_bijective h (Or.inr rfl) y).1
    apply (left_bijective h y).1
    change f y (f (middle .e1279 f x y) y) = f y (f a y)
    rw [hb, hc]
    exact h x y
  by_cases hb : f a y = b <;> by_cases hq : middle .e1279 f x y = b <;>
    by_cases hc : f y b = x <;>
    simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]

def rowUnits (r : Fin 13 → Fin 13) : CNF (Atom 13) :=
  all1 fun y => ⟨#[[(p 0 y (r y), true)]]⟩

def symmetry (i : Fin 272) : CNF (Atom 13) :=
  (all1 fun z => if allowed i [0,1] z then .empty else ⟨#[[(p 1 1 z,false)]]⟩) ++
  (all1 fun z => all1 fun t => if allowed i [0,1,z] t then .empty else
    ⟨#[[(p 1 1 z,false), (p 1 0 t,false)]]⟩)

theorem model_symmetry (i : Fin 272) (f : Fin 13 → Fin 13 → Fin 13)
    (hz : allowed i [0,1] (f 1 1) = true)
    (ht : allowed i [0,1,f 1 1] (f 1 0) = true) :
    (symmetry i).Sat (meaning .e1279 f) := by
  apply sat_append
  · apply sat_all1; intro z
    split
    · exact CNF.sat_empty
    · rename_i hn
      apply sat_single
      have he : f 1 1 ≠ z := by intro he; subst z; exact hn hz
      simp [CNF.Clause.eval, meaning, p, he]
  · apply sat_all1; intro z
    apply sat_all1; intro t
    split
    · exact CNF.sat_empty
    · rename_i hn
      apply sat_single
      by_cases he : f 1 1 = z
      · have he' : f 1 0 ≠ t := by intro he'; subst z; subst t; exact hn ht
        simp [CNF.Clause.eval, meaning, p, he']
      · simp [CNF.Clause.eval, meaning, p, he]

def formula (i : Fin 272) : CNF (Atom 13) :=
  Encoding.formula .e1279 13 ++ cancellation ++ rowUnits (row i) ++ symmetry i

/-- Cache the common constraints instead of rebuilding them for all 272 cases. -/
def natBase : CNF ℕ :=
  sanitize ((Encoding.formula .e1279 13 ++ cancellation).relabel code)

def natFormulaWith (base : CNF ℕ) (i : Fin 272) : CNF ℕ :=
  base ++ sanitize ((rowUnits (row i)).relabel code) ++
    sanitize ((symmetry i).relabel code)

def natFormula (i : Fin 272) : CNF ℕ := natFormulaWith natBase i

private theorem sanitize_append (F G : CNF ℕ) : sanitize (F ++ G) = sanitize F ++ sanitize G := by
  change (⟨(F.clauses ++ G.clauses).filter _⟩ : CNF ℕ) =
    ⟨F.clauses.filter _ ++ G.clauses.filter _⟩
  rw [Array.filter_append]
  simp

private theorem natFormula_eq (i : Fin 272) : natFormula i = sanitize ((formula i).relabel code) := by
  simp only [natFormula, natFormulaWith, natBase, formula, CNF.relabel_append, sanitize_append]

theorem model_formula (i : Fin 272) (f : Fin 13 → Fin 13 → Fin 13) (h : Holds .e1279 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hr : f 0 = row i)
    (hz : allowed i [0,1] (f 1 1) = true)
    (ht : allowed i [0,1,f 1 1] (f 1 0) = true) :
    (formula i).Sat (meaning .e1279 f) := by
  apply sat_append
  · apply sat_append
    · apply sat_append
      · apply Encoding.model_formula .e1279 f h hd
        simpa only [hr] using row_chain i
      · exact model_cancellation f h
    · apply sat_all1; intro y
      apply sat_single
      simp [CNF.Clause.eval, meaning, p, hr]
  · exact model_symmetry i f hz ht

theorem no_model_of_unsat (i : Fin 272) (f : Fin 13 → Fin 13 → Fin 13) (h : Holds .e1279 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hr : f 0 = row i)
    (hz : allowed i [0,1] (f 1 1) = true)
    (ht : allowed i [0,1,f 1 1] (f 1 0) = true)
    (hn : (natFormula i).Unsat) : False := by
  have unsat_raw : ((formula i).relabel code).Unsat := by
    intro a
    cases he : (((formula i).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula i).Sat a := by
        rw [natFormula_eq]
        simp only [CNF.Sat, CNF.eval, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      exact Bool.noConfusion hh
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hn' (meaning .e1279 f)
  rw [model_formula i f h hd hr hz ht] at hh
  exact Bool.noConfusion hh

end Spectrum.SmallPairs.OrderThirteen
