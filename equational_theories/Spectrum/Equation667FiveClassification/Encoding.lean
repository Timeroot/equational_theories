import equational_theories.Spectrum.Equation667RightIdentityTwelve.Encoding
import equational_theories.Spectrum.Equation667FiberThree
import Mathlib.Data.Fin.VecNotation

/-! Unique normalized idempotent-free E667 operation on five points.
Only the final fixed-row table check is delegated to the LRAT certificate;
normalization uses a small unary-permutation lemma and the proved cycle rules. -/
namespace Spectrum.E667.FiveClassification
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open SmallPairs.Encoding (Atom p code code_injective)
open RightIdentityTwelve (Holds meaning)

abbrev K := Fin 5

def swap : K ≃ K := Equiv.swap 2 4
def canonical (x y : K) : K := swap (FiberThree.quotient (swap x) (swap y))
def row : CNF (Atom 5) := all1 fun y => ⟨#[[(p 0 y (canonical 0 y),true)]]⟩
def free : CNF (Atom 5) := all1 fun x => ⟨#[[(p x x x,false)]]⟩
def different : CNF (Atom 5) :=
  ⟨#[(List.finRange 5).flatMap fun x => (List.finRange 5).map fun y =>
    (p x y (canonical x y),false)]⟩
def formula : CNF (Atom 5) :=
  RightIdentityTwelve.latin ++ RightIdentityTwelve.identities ++ row ++ free ++ different

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
    (hr : ∀ y, f 0 y = canonical 0 y) (hf : ∀ x, f x x ≠ x) : f = canonical := by
  classical
  by_contra he
  have hex : ∃ x y, f x y ≠ canonical x y := by
    by_contra hh
    push Not at hh
    exact he (funext fun x => funext fun y => hh x y)
  have hsrow : row.Sat (meaning f) := by
    apply sat_all1; intro y
    apply sat_single
    simp [CNF.Clause.eval, meaning, p, hr]
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
    exact sat_append _ _ _ (sat_append _ _ _ (sat_append _ _ _
      (sat_append _ _ _ (RightIdentityTwelve.model_latin f h)
        (RightIdentityTwelve.model_identities f h)) hsrow) hsfree) hsdiff
  exact contradiction_of_sat formula (meaning f)
    (unsat_of_sanitized formula code code_injective hn) hs

private theorem row_unique : ∀ r : K → K, Function.Injective r →
    (∃ y, r y = y) → r 0 ≠ 0 → r (r 0) ≠ 0 → r (r (r 0)) ≠ 0 →
    (∀ y, (r y).val ≤ y.val + 1) → r = ![1,2,3,0,4] := by
  set_option maxHeartbeats 2000000 in
  set_option synthInstance.maxSize 2000 in
  decide +kernel

private theorem row_canonical : canonical 0 = ![1,2,3,0,4] := by decide +kernel

/-- A row with a fixed point must consist of a four-cycle through its own
index and the remaining fixed point. The cycle is labelled by the already
proved chain-labelling theorem. -/
theorem normalize_free (f : K → K → K) (h : Holds f) (hf : ∀ x, f x x ≠ x) :
    ∃ e : K ≃ K, ∀ y, e (f (e.symm 0) (e.symm y)) = canonical 0 y := by
  classical
  obtain ⟨a,ha⟩ := (RightIdentityTwelve.right_bijective h 0).2 0
  let s := Equiv.swap a (0 : K)
  let g (x y : K) := s (f (s.symm x) (s.symm y))
  have hg : Holds g := RightIdentityTwelve.holds_relabel h s
  have gfree (x : K) : g x x ≠ x := by
    intro hh
    have := congrArg s.symm hh
    simp only [g, Equiv.symm_apply_apply] at this
    exact hf (s.symm x) this
  have s0 : s.symm 0 = a := Equiv.swap_apply_right a 0
  have gfix : g 0 (s 0) = s 0 := by
    simp only [g, s0, Equiv.symm_apply_apply, ha]
  obtain ⟨e,he,hchain⟩ := E63.OrderTen.exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let q (x y : K) := e (g (e.symm x) (e.symm y))
  have hq : Holds q := RightIdentityTwelve.holds_relabel hg e
  have qfree (x : K) : q x x ≠ x := by
    intro hh
    have := congrArg e.symm hh
    simp only [q, Equiv.symm_apply_apply] at this
    exact gfree (e.symm x) this
  letI : Magma K := ⟨q⟩
  have law : Equation667 K := fun x y => (hq x y).symm
  have h2 : q 0 (q 0 0) ≠ 0 := by
    intro hh
    exact qfree (q 0 0) (two_cycle_square_idempotent law 0 hh)
  have h3 : q 0 (q 0 (q 0 0)) ≠ 0 := by
    intro hh
    exact qfree 0 (three_cycle_implies_idempotent law 0 hh)
  have hr : q 0 = canonical 0 := by
    rw [row_canonical]
    apply row_unique (q 0) (RightIdentityTwelve.left_bijective hq 0).1
    · refine ⟨e (s 0), ?_⟩
      simp only [q, he', Equiv.symm_apply_apply, gfix]
    · exact qfree 0
    · exact h2
    · exact h3
    · intro y
      simpa only [q, he'] using hchain y
  refine ⟨s.trans e, fun y => ?_⟩
  have hh := congrFun hr y
  simpa only [q, g, Equiv.trans_apply, Equiv.symm_trans_apply, he'] using hh

/-- Every idempotent-free five-point E667 operation is isomorphic to
`3x+3y+1` over `Fin 5`. -/
theorem classification (hn : natFormula.Unsat) (f : K → K → K)
    (h : Holds f) (hf : ∀ x, f x x ≠ x) :
    ∃ e : K ≃ K, ∀ x y, e (f x y) = FiberThree.quotient (e x) (e y) := by
  classical
  obtain ⟨e,hr⟩ := normalize_free f h hf
  let g (x y : K) := e (f (e.symm x) (e.symm y))
  have hg : Holds g := RightIdentityTwelve.holds_relabel h e
  have gf (x : K) : g x x ≠ x := by
    intro hh
    have := congrArg e.symm hh
    simp only [g, Equiv.symm_apply_apply] at this
    exact hf (e.symm x) this
  have eqg : g = canonical := normalized_unique hn g hg hr gf
  refine ⟨e.trans swap, fun x y => ?_⟩
  have hh := congrFun (congrFun eqg (e x)) (e y)
  simp only [g, Equiv.symm_apply_apply, canonical] at hh
  change swap (e (f x y)) = _
  rw [hh]
  exact Equiv.swap_apply_self 2 4 _

end Spectrum.E667.FiveClassification
