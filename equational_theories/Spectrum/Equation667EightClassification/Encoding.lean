import equational_theories.Spectrum.Equation667RightIdentityTwelve.Encoding
import equational_theories.Spectrum.Equation667EightBase
import Mathlib.Data.Fin.VecNotation

/-! Classification after chain-labelling a row with a fixed point.
The certificate checks the full eight-point table; normalization is proved. -/
namespace Spectrum.E667.EightClassification
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open SmallPairs.Encoding (Atom p code code_injective)
open RightIdentityTwelve (Holds meaning)

abbrev K := Fin 8

abbrev canonical := Eight.quotient
def fixed : CNF (Atom 8) :=
  ⟨#[(List.finRange 8).map fun y => (p 0 y y,true)]⟩
def free : CNF (Atom 8) := all1 fun x => ⟨#[[(p x x x,false)]]⟩
def different : CNF (Atom 8) :=
  ⟨#[(List.finRange 8).flatMap fun x => (List.finRange 8).map fun y =>
    (p x y (canonical x y),false)]⟩
def formula : CNF (Atom 8) :=
  RightIdentityTwelve.latin ++ RightIdentityTwelve.identities ++ RightIdentityTwelve.chain ++ fixed ++ free ++ different

def natFormula : CNF ℕ := sanitize (formula.relabel code)

private theorem unsat_of_sanitized {α : Type} (F : CNF α) (c : α → ℕ)
    (hc : Function.Injective c) (hn : (sanitize (F.relabel c)).Unsat) : F.Unsat := by
  have raw : (F.relabel c).Unsat := by
    intro a
    cases he : (F.relabel c).eval a with
    | false => rfl
    | true =>
      have hs : (sanitize (F.relabel c)).Sat a := by
        simp only [CNF.Sat, CNF.eval, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun cl hcl => he cl (Array.mem_filter.mp hcl).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  exact (CNF.unsat_relabel_iff (fun _ _ he => hc he)).mp raw

private theorem contradiction_of_sat {α : Type} (F : CNF α) (m : α → Bool)
    (hu : F.Unsat) (hs : F.Sat m) : False := by
  have hh := hu m
  rw [hs] at hh
  contradiction

theorem normalized_unique (hn : natFormula.Unsat) (f : K → K → K) (h : Holds f)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) (hr : ∃ y, f 0 y = y) (hf : ∀ x, f x x ≠ x) : f = canonical := by
  classical
  by_contra he
  have hex : ∃ x y, f x y ≠ canonical x y := by
    by_contra hh
    push Not at hh
    exact he (funext fun x => funext fun y => hh x y)
  have hsfixed : fixed.Sat (meaning f) := by
    obtain ⟨y,hy⟩ := hr
    apply sat_single
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨y, List.mem_finRange _, by simp [meaning, p, hy]⟩
  have hsfree : free.Sat (meaning f) := by
    apply sat_all1; intro x
    apply sat_single
    simp [CNF.Clause.eval, meaning, p, hf]
  have hsdiff : different.Sat (meaning f) := by
    obtain ⟨x,y,hxy⟩ := hex
    apply sat_single
    simp only [CNF.Clause.eval, List.any_flatMap, List.any_map, List.any_eq_true]
    exact ⟨x, List.mem_finRange _, y, List.mem_finRange _, by simp [meaning, p, hxy]⟩
  have hs : formula.Sat (meaning f) := by
    simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨RightIdentityTwelve.model_latin f h,
      RightIdentityTwelve.model_identities f h⟩,
      RightIdentityTwelve.model_chain f hc⟩, hsfixed⟩, hsfree⟩, hsdiff⟩

  exact contradiction_of_sat formula (meaning f)
    (unsat_of_sanitized formula code code_injective hn) hs

/-- Every finite Latin square has a row with a fixed point. Move its index to
zero, then conjugate its translation into chain form while fixing zero. -/
theorem normalize_free (f : K → K → K) (h : Holds f) :
    ∃ e : K ≃ K,
      (∀ y, (e (f (e.symm 0) (e.symm y))).val ≤ y.val + 1) ∧
      (∃ y, e (f (e.symm 0) (e.symm y)) = y) := by
  classical
  obtain ⟨a,ha⟩ := (RightIdentityTwelve.right_bijective h 0).2 0
  let s := Equiv.swap a (0 : K)
  let g (x y : K) := s (f (s.symm x) (s.symm y))
  have s0 : s.symm 0 = a := Equiv.swap_apply_right a 0
  have gfix : g 0 (s 0) = s 0 := by
    simp only [g, s0, Equiv.symm_apply_apply, ha]
  obtain ⟨e,he,hchain⟩ := E63.OrderTen.exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  refine ⟨s.trans e, ?_, e (s 0), ?_⟩
  · intro y
    simpa only [g, Equiv.trans_apply, Equiv.symm_trans_apply, he'] using hchain y
  · simp only [Equiv.trans_apply, Equiv.symm_trans_apply, he',
      Equiv.symm_apply_apply, s0, ha]

/-- All idempotent-free eight-point E667 models are isomorphic. -/
theorem classification (hn : natFormula.Unsat) (f : K → K → K)
    (h : Holds f) (hf : ∀ x, f x x ≠ x) :
    ∃ e : K ≃ K, ∀ x y, e (f x y) = canonical (e x) (e y) := by
  classical
  obtain ⟨e,hc,hr⟩ := normalize_free f h
  let g (x y : K) := e (f (e.symm x) (e.symm y))
  have hg : Holds g := RightIdentityTwelve.holds_relabel h e
  have gf (x : K) : g x x ≠ x := by
    intro hh
    have := congrArg e.symm hh
    simp only [g, Equiv.symm_apply_apply] at this
    exact hf (e.symm x) this
  have eqg : g = canonical := normalized_unique hn g hg hc hr gf
  refine ⟨e, fun x y => ?_⟩
  have hh := congrFun (congrFun eqg (e x)) (e y)
  simpa only [g, Equiv.symm_apply_apply] using hh

end Spectrum.E667.EightClassification
