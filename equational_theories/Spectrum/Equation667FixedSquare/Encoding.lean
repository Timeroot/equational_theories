import equational_theories.Spectrum.Equation667RightIdentityTwelve.Certificate
import equational_theories.Spectrum.Equation667SquareCases

/-! A fixed square map removes the auxiliary table from the E667 search.
All clauses have algebraic soundness proofs. No nonexistence assertion is made
without a separately checked refutation of the resulting finite formula. -/
namespace Spectrum.E667.FixedSquare
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open SmallPairs.Encoding (Atom p code code_injective)
open RightIdentityTwelve (Holds meaning latin threeCycles twoCycles fibers
  left_bijective model_latin model_threeCycles model_twoCycles model_fibers)
variable {n : ℕ}

def cubic (d : Fin n → Fin n) : CNF (Atom n) :=
  all1 fun x => all1 fun y => all1 fun a => all1 fun b =>
    ⟨#[[(p (d x) y a,false),(p x a b,false),(p y b x,true)],
       [(p (d x) y a,false),(p x a b,true),(p y b x,false)],
       [(p (d x) y a,true),(p x a b,false),(p y b x,false)]]⟩

def square (d : Fin n → Fin n) : CNF (Atom n) :=
  all1 fun x => ⟨#[[(p x x (d x),true)]]⟩

def nonidempotent : CNF (Atom n) :=
  ⟨#[(List.finRange n).map (fun x => (p x x x,false))]⟩

def noRightIdentity : CNF (Atom n) := all1 fun e =>
  ⟨#[(List.finRange n).map (fun x => (p x e x,false))]⟩

def badPair (d : Fin n → Fin n) (x y : Fin n) : CNF (Atom n) :=
  all1 fun z => ⟨#[[(p x y z,false),(p (d x) (d y) (d z),false)]]⟩

theorem model_cubic (f : Fin n → Fin n → Fin n) (h : Holds f)
    (d : Fin n → Fin n) (hd : ∀ x, f x x = d x) :
    (cubic d).Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  have he : f y (f x (f (d x) y)) = x := by simpa only [hd] using h x y
  have hab (ha : f (d x) y = a) (hb : f x a = b) : f y b = x := by
    simpa only [ha,hb] using he
  have hac (ha : f (d x) y = a) (hc : f y b = x) : f x a = b := by
    apply (left_bijective h y).1
    simpa only [ha,hc] using he
  have hbc (hb : f x a = b) (hc : f y b = x) : f (d x) y = a := by
    apply (left_bijective h x).1
    apply (left_bijective h y).1
    simpa only [hb,hc] using he
  by_cases ha : f (d x) y = a <;> by_cases hb : f x a = b <;>
    by_cases hc : f y b = x <;>
      simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p]

theorem model_square (f : Fin n → Fin n → Fin n)
    (d : Fin n → Fin n) (hd : ∀ x, f x x = d x) :
    (square d).Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_single
  simp [CNF.Clause.eval, meaning, p, hd]

theorem model_nonidempotent (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) :
    nonidempotent.Sat (meaning f) := by
  classical
  letI : Magma (Fin 12) := ⟨f⟩
  have hh := not_idempotent_twelve (fun x y => (h x y).symm) (by simp)
  push Not at hh
  obtain ⟨x,hx⟩ := hh
  apply sat_single
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨x, List.mem_finRange _, by simpa [meaning,p] using hx⟩

theorem model_noRightIdentity (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) :
    noRightIdentity.Sat (meaning f) := by
  classical
  letI : Magma (Fin 12) := ⟨f⟩
  apply sat_all1; intro e
  have hh := not_right_identity_twelve (fun x y => (h x y).symm) (by simp) e
  push Not at hh
  obtain ⟨x,hx⟩ := hh
  apply sat_single
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨x, List.mem_finRange _, by simpa [meaning,p] using hx⟩

theorem model_badPair (f : Fin n → Fin n → Fin n)
    (d : Fin n → Fin n) (x y : Fin n) (hb : d (f x y) ≠ f (d x) (d y)) :
    (badPair d x y).Sat (meaning f) := by
  apply sat_all1; intro z
  apply sat_single
  have hb' := Ne.symm hb
  by_cases hz : f x y = z <;> simp_all [CNF.Clause.eval, meaning, p]

def formula (d : Fin 12 → Fin 12) : CNF (Atom 12) :=
  latin ++ cubic d ++ square d ++ nonidempotent ++ noRightIdentity ++
    threeCycles ++ twoCycles ++ fibers

theorem model_formula (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (d : Fin 12 → Fin 12) (hd : ∀ x, f x x = d x) :
    (formula d).Sat (meaning f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨model_latin f h, model_cubic f h d hd⟩, model_square f d hd⟩,
    model_nonidempotent f h⟩, model_noRightIdentity f h⟩, model_threeCycles f h⟩,
    model_twoCycles f h⟩, model_fibers f h⟩

def natFormula (d : Fin 12 → Fin 12) : CNF ℕ :=
  sanitize ((formula d).relabel code)

theorem no_model (d : Fin 12 → Fin 12) (hn : (natFormula d).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hd : ∀ x, f x x = d x) : False := by
  have raw : ((formula d).relabel code).Unsat := by
    intro a
    cases he : ((formula d).relabel code).eval a with
    | false => rfl
    | true =>
      have hs : (natFormula d).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hh := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp raw (meaning f)
  rw [model_formula f h d hd] at hh
  contradiction

spectrum_assert model_formula complete
spectrum_assert model_badPair complete
spectrum_assert no_model complete
end Spectrum.E667.FixedSquare
