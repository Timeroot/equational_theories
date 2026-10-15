import equational_theories.Spectrum.SmallOrders.Encoding
import equational_theories.Generated.FiniteImplicationSearch.theorems.Inverses1

/-! Finite E1076 magmas are idempotent quasigroups. A left translation has
no nontrivial two-cycle: if `x * (x * y) = y`, the defining identity immediately
reduces to `x = y`. Record this consequence explicitly in the small-order CNF.
-/
namespace Spectrum.E1076.ShortCycles
open Std.Sat Spectrum.SmallOrders
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize exactlyOne sat_exactlyOne)
open SmallOrders.Encoding (Atom p q meaning code code_injective)

theorem idempotent {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1076 f) (x : A) : f x x = x := by
  letI : Magma A := ⟨f⟩
  exact (Finite.Equation1076_implies_Equation3 A (fun x y => (h x y).symm) x).symm

theorem no_two_cycle {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1076 f) {x y : A} (hxy : x ≠ y) : f x (f x y) ≠ y := by
  intro he
  have hh : f y (f (f x (f x y)) y) = x := h x y
  rw [he, idempotent h y, idempotent h y] at hh
  exact hxy hh.symm

theorem no_triangle {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1076 f) {x y : A} (hxy : x ≠ y) : f y (f x y) ≠ x := by
  intro he
  have hh : f y (f (f x (f x y)) y) = x := h x y
  have hq : f x (f x y) = x :=
    (right_bijective h rfl y).1 ((left_bijective h y).1 (hh.trans he.symm))
  have ha : f x y = x := (left_bijective h x).1 (hq.trans (idempotent h x).symm)
  have hb : y = x := (left_bijective h x).1 (ha.trans (idempotent h x).symm)
  exact hxy hb.symm

variable {n : ℕ} [NeZero n]

def diagonal : CNF (Atom n) := all1 fun x => ⟨#[[(p x x x, true)]]⟩

def twoCycles : CNF (Atom n) := all1 fun x => all1 fun y => all1 fun z =>
  if x ≠ y then ⟨#[[(p x y z, false), (p x z y, false)]]⟩ else .empty

def middleCycles : CNF (Atom n) := all1 fun x => all1 fun y =>
  if x ≠ y then ⟨#[[(q x y y, false)]]⟩ else .empty

def middleLatin : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => q x z y) ++ exactlyOne (fun z => q z x y)

def formula (n : ℕ) [NeZero n] : CNF (Atom n) :=
  Encoding.formula .e1076 n ++ diagonal ++ twoCycles ++ middleCycles ++ middleLatin

def natFormula (n : ℕ) [NeZero n] : CNF ℕ :=
  sanitize ((formula n).relabel code)

omit [NeZero n] in
lemma model_diagonal (f : Fin n → Fin n → Fin n) (h : Holds .e1076 f) :
    diagonal.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_single
  simp [CNF.Clause.eval, meaning, p, idempotent h]

omit [NeZero n] in
lemma model_twoCycles (f : Fin n → Fin n → Fin n) (h : Holds .e1076 f) :
    twoCycles.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hxy
    apply sat_single
    by_cases hxz : f x y = z
    · have hz : f x z ≠ y := by
        simpa only [hxz] using no_two_cycle h hxy
      simp [CNF.Clause.eval, meaning, p, hz]
    · simp [CNF.Clause.eval, meaning, p, hxz]
  · exact CNF.sat_empty

omit [NeZero n] in
lemma model_middleCycles (f : Fin n → Fin n → Fin n) (h : Holds .e1076 f) :
    middleCycles.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  split
  · rename_i hxy
    apply sat_single
    have hh : middle .e1076 f x y ≠ y := no_two_cycle h hxy
    simp [CNF.Clause.eval, meaning, q, hh]
  · exact CNF.sat_empty

theorem middle_left_bijective {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1076 f) (x : A) : Function.Bijective (middle .e1076 f x) :=
  (left_bijective h x).comp (left_bijective h x)

theorem middle_right_bijective {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1076 f) (y : A) : Function.Bijective (fun x => middle .e1076 f x y) := by
  have hi : Function.Injective (fun x => middle .e1076 f x y) := by
    intro x z hxz
    change middle .e1076 f x y = middle .e1076 f z y at hxz
    have hx := h x y
    have hz := h z y
    change f y (f (middle .e1076 f x y) y) = x at hx
    change f y (f (middle .e1076 f z y) y) = z at hz
    rw [hxz] at hx
    exact hx.symm.trans hz
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

omit [NeZero n] in
lemma model_middleLatin (f : Fin n → Fin n → Fin n) (h : Holds .e1076 f) :
    middleLatin.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := (middle_left_bijective h x).2 y
      exact ⟨z, by simp [meaning,hz]⟩
    · intro z w hz hw
      simp only [meaning,Fin.reduceEq,↓reduceIte,decide_eq_true_eq] at hz hw
      exact (middle_left_bijective h x).1 (hz.trans hw.symm)
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := (middle_right_bijective h x).2 y
      exact ⟨z, by simp [meaning,hz]⟩
    · intro z w hz hw
      simp only [meaning,Fin.reduceEq,↓reduceIte,decide_eq_true_eq] at hz hw
      exact (middle_right_bijective h x).1 (hz.trans hw.symm)

lemma model_formula (f : Fin n → Fin n → Fin n) (h : Holds .e1076 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    (formula n).Sat (meaning .e1076 f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨Encoding.model_formula .e1076 f h hd hc, model_diagonal f h⟩,
    model_twoCycles f h⟩, model_middleCycles f h⟩, model_middleLatin f h⟩

theorem not_hasModel (hn : (natFormula n).Unsat) : ¬ Law1076.HasModel n := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf, hd, hc⟩ := normalized M.op ((holds_iff .e1076 M).mpr hM)
  have unsat_raw : ((formula n).relabel code).Unsat := by
    intro a
    cases he : (((formula n).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula n).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hu := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hu (meaning .e1076 f)
  rw [model_formula f hf hd hc] at hh
  contradiction

end Spectrum.E1076.ShortCycles
