import equational_theories.Spectrum.SmallOrders.Encoding
import equational_theories.Definability.Cancel1516

/-! The square-headed law E1516. Its proved finite quasigroup and squaring
properties make a short two-layer exclusion certificate possible. -/
namespace Spectrum.SmallOrders.SquareOuter
open Std.Sat
open E63.OrderTen.Encoding (all1 exactlyOne sat_all1 sat_single sat_append sat_exactlyOne sanitize)

def Holds {A : Type*} (f : A → A → A) : Prop := ∀ x y, f (f y y) (f x (f x y)) = x

theorem holds_iff {A : Type*} (M : Magma A) : Holds M.op ↔ @satisfies _ A M Law1516 := by
  rw [Law1516.models_iff]
  exact forall_congr' fun _ => forall_congr' fun _ => eq_comm

theorem left_injective {A : Type} [Finite A] {f : A → A → A} (h : Holds f) (x : A) :
    Function.Injective (f x) :=
  Law.MagmaLaw.injLeft_Equation1516 A ⟨f⟩ ((holds_iff ⟨f⟩).mp h) x

theorem right_injective {A : Type} [Finite A] {f : A → A → A} (h : Holds f) (y : A) :
    Function.Injective (fun x => f x y) :=
  Law.MagmaLaw.injRight_Equation1516 A ⟨f⟩ ((holds_iff ⟨f⟩).mp h) y

theorem square_bijective {A : Type} [Finite A] {f : A → A → A} (h : Holds f) :
    Function.Bijective (fun x => f x x) := by
  have hs := Law.MagmaLaw.sqSurj_Equation1516 ⟨f⟩ ((holds_iff ⟨f⟩).mp h)
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem holds_relabel {A : Type*} {f : A → A → A} (h : Holds f) (e : A ≃ A) :
    Holds (fun x y => e (f (e.symm x) (e.symm y))) := by
  intro x y
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    using congrArg e (h (e.symm x) (e.symm y))

theorem normalized {n : ℕ} [NeZero n]
    (f : Fin n → Fin n → Fin n) (h : Holds f) :
    ∃ g : Fin n → Fin n → Fin n, Holds g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧ (∀ y, (g 0 y).val ≤ y.val + 1) := by
  classical
  have choose_zero : ∃ g : Fin n → Fin n → Fin n, Holds g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) := by
    by_cases hi : ∀ x, f x x = x
    · exact ⟨f, h, fun _ => hi⟩
    · push Not at hi
      obtain ⟨x, hx⟩ := hi
      let e := Equiv.swap x (0 : Fin n)
      let g (a b : Fin n) := e (f (e.symm a) (e.symm b))
      refine ⟨g, holds_relabel h e, fun hg => ?_⟩
      have he : e.symm 0 = x := Equiv.swap_apply_right x 0
      have : f x x = x := by
        apply e.injective
        simpa only [g, he, e, Equiv.swap_apply_left] using hg
      exact (hx this).elim
  obtain ⟨g, hg, hi⟩ := choose_zero
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let q (a b : Fin n) := e (g (e.symm a) (e.symm b))
  refine ⟨q, holds_relabel hg e, ?_, ?_⟩
  · intro hq x
    have h0 : g 0 0 = 0 := by
      apply e.injective
      simpa only [q, he', he] using hq
    simp only [q, hi h0, Equiv.apply_symm_apply]
  · intro y
    simpa only [q, he'] using hc y


variable {n : ℕ} [NeZero n]
abbrev Atom (n : ℕ) := Fin 2 × Fin n × Fin n × Fin n
abbrev p (x y z : Fin n) : Atom n := (0,x,y,z)
abbrev q (x y z : Fin n) : Atom n := (1,x,y,z)

def meaning (f : Fin n → Fin n → Fin n) (a : Atom n) : Bool :=
  if a.1 = 0 then decide (f a.2.1 a.2.2.1 = a.2.2.2)
  else decide (f a.2.1 (f a.2.1 a.2.2.1) = a.2.2.2)

def latin : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => p x y z) ++ exactlyOne (fun z => p x z y) ++
    exactlyOne (fun z => p z x y)

def inner (x y : Fin n) : CNF (Atom n) := all1 fun a => all1 fun b =>
  ⟨#[[(p x y a,false),(p x a b,false),(q x y b,true)],
     [(p x y a,false),(p x a b,true),(q x y b,false)],
     [(p x y a,true),(p x a b,false),(q x y b,false)]]⟩

def outer (x y : Fin n) : CNF (Atom n) := all1 fun a => all1 fun b =>
  ⟨#[[(p y y a,false),(q x y b,false),(p a b x,true)],
     [(p y y a,false),(q x y b,true),(p a b x,false)]]⟩

def identities : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => q x y z) ++ inner x y ++ outer x y

def diagonal : CNF (Atom n) := all1 fun x => ⟨#[[(p 0 0 0,false),(p x x x,true)]]⟩
def chain : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + 1 < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty
def squares : CNF (Atom n) :=
  all1 fun y => exactlyOne (fun x => p x x y)

def formula (n : ℕ) [NeZero n] : CNF (Atom n) :=
  latin ++ identities ++ diagonal ++ chain ++ squares

omit [NeZero n] in
lemma model_latin (f : Fin n → Fin n → Fin n) (h : Holds f) : latin.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨f x y, by simp [meaning]⟩
      · intro z w hz hw
        simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
        exact hz.symm.trans hw
    · apply sat_exactlyOne
      · obtain ⟨z,hz⟩ := Finite.surjective_of_injective (left_injective h x) y
        exact ⟨z, by simp [meaning, hz]⟩
      · intro z w hz hw
        simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
        exact left_injective h x (hz.trans hw.symm)
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := Finite.surjective_of_injective (right_injective h x) y
      exact ⟨z, by simp [meaning, hz]⟩
    · intro z w hz hw
      simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
      exact right_injective h x (hz.trans hw.symm)

omit [NeZero n] in
lemma model_inner (f : Fin n → Fin n → Fin n) (h : Holds f) (x y : Fin n) :
    (inner x y).Sat (meaning f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  by_cases ha : f x y = a
  · by_cases hb : f x a = b <;> simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]
  · have hb : f x a = b → f x (f x y) = b → False := by
      intro hb hc
      exact ha (left_injective h x (hc.trans hb.symm))
    by_cases hc : f x (f x y) = b
    · have hd : f x a ≠ b := fun he => hb he hc
      simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha, hd]
    · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha, hc]

omit [NeZero n] in
lemma model_outer (f : Fin n → Fin n → Fin n) (h : Holds f) (x y : Fin n) :
    (outer x y).Sat (meaning f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  by_cases ha : f y y = a
  · have he := h x y
    rw [ha] at he
    have hh : f x (f x y) = b ↔ f a b = x := by
      constructor
      · intro hb; rwa [hb] at he
      · intro hb; exact left_injective h a (he.trans hb.symm)
    by_cases hb : f a b = x <;> simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]
  · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha]

omit [NeZero n] in
lemma model_identities (f : Fin n → Fin n → Fin n) (h : Holds f) :
    (identities).Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨f x (f x y), by simp [meaning]⟩
      · intro z w hz hw
        simp [meaning] at hz hw
        exact hz.symm.trans hw
    · exact model_inner f h x y
  · exact model_outer f h x y

lemma model_diagonal (f : Fin n → Fin n → Fin n)
    (h : f 0 0 = 0 → ∀ x, f x x = x) : diagonal.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_single
  by_cases h0 : f 0 0 = 0 <;> simp_all [CNF.Clause.eval, meaning, p]

lemma model_chain (f : Fin n → Fin n → Fin n)
    (h : ∀ y, (f 0 y).val ≤ y.val + 1) : chain.Sat (meaning f) := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hyz
    apply sat_single
    have hh : f 0 y ≠ z := by
      intro he
      have := h y
      rw [he] at this
      omega
    simp [CNF.Clause.eval, meaning, p, hh]
  · exact CNF.sat_empty


omit [NeZero n] in
lemma model_squares (f : Fin n → Fin n → Fin n) (h : Holds f) :
    (squares).Sat (meaning f) := by
  apply sat_all1; intro y
  apply sat_exactlyOne
  · obtain ⟨z,hz⟩ := (square_bijective h).2 y
    exact ⟨z, by simp [meaning, hz]⟩
  · intro z w hz hw
    simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
    exact (square_bijective h).1 (hz.trans hw.symm)

lemma model_formula (f : Fin n → Fin n → Fin n) (h : Holds f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    (formula n).Sat (meaning f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨model_latin f h, model_identities f h⟩, model_diagonal f hd⟩,
    model_chain f hc⟩, model_squares f h⟩

abbrev code := @SmallPairs.Encoding.code n

lemma code_injective : Function.Injective (@code n) := SmallPairs.Encoding.code_injective

def natFormula (n : ℕ) [NeZero n] : CNF ℕ :=
  sanitize ((formula n).relabel code)

lemma no_model_of_unsat (hn : (natFormula n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : False := by
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
  have hh := hn' (meaning f)
  rw [model_formula f h hd hc] at hh
  contradiction

theorem not_hasModel (hn : (natFormula n).Unsat) : ¬ Law1516.HasModel n := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf, hd, hc⟩ := normalized M.op ((holds_iff M).mpr hM)
  exact no_model_of_unsat hn f hf hd hc

end Spectrum.SmallOrders.SquareOuter
