import equational_theories.Spectrum.Equation907.OrderTen.Normalization
import equational_theories.Spectrum.Equation63.OrderTen.Encoding

/-! One-hot E907 encoding. Every clause follows from the law, finite left
cancellation, normalization, or the proved pointed-cycle exclusions. -/
namespace Spectrum.E907.OrderTen.Encoding
open Std.Sat
open E63.OrderTen.Encoding (Atom p meaning all1 exactlyOne sat_all1 sat_single
  sat_append sat_exactlyOne sanitize code code_injective diagonal chain
  model_diagonal model_chain)
variable {n : ℕ} [NeZero n]

def latin : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => p x y z) ++ exactlyOne (fun z => p x z y)

def identities : CNF (Atom n) := all1 fun x => all1 fun y =>
  all1 fun a => all1 fun b => all1 fun c =>
  ⟨#[[(p y x a,false),(p x y b,false),(p a b c,false),(p y c x,true)],
     [(p y x a,false),(p x y b,false),(p a b c,true),(p y c x,false)]]⟩

def shortTwo (a : Fin n) : CNF (Atom n) := all1 fun b =>
  if b ≠ a then ⟨#[[(p a a b,false),(p a b a,false)]]⟩ else .empty

def shortThree (a : Fin n) : CNF (Atom n) := all1 fun b => all1 fun c =>
  if b ≠ a ∧ c ≠ a ∧ c ≠ b then
    ⟨#[[(p a a b,false),(p a b c,false),(p a c a,false)]]⟩ else .empty

def shortFour (a : Fin n) : CNF (Atom n) :=
  all1 fun b => all1 fun c => all1 fun d =>
  if b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c then
    ⟨#[[(p a a b,false),(p a b c,false),(p a c d,false),(p a d a,false)]]⟩
  else .empty

def cycles : CNF (Atom n) := all1 fun a => shortTwo a ++ shortThree a ++ shortFour a

def formula (n : ℕ) [NeZero n] : CNF (Atom n) :=
  latin ++ identities ++ diagonal ++ chain ++ cycles

omit [NeZero n] in
lemma model_latin (f : Fin n → Fin n → Fin n) (h : Holds f) : latin.Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_exactlyOne
    · exact ⟨f x y, by simp [meaning]⟩
    · intro z w hz hw
      simp only [meaning, decide_eq_true_eq] at hz hw
      exact hz.symm.trans hw
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := E907.left_surjective h x y
      exact ⟨z, by simpa [meaning] using hz⟩
    · intro z w hz hw
      simp only [meaning, decide_eq_true_eq] at hz hw
      exact E907.left_injective h x (hz.trans hw.symm)

omit [NeZero n] in
lemma model_identities (f : Fin n → Fin n → Fin n) (h : Holds f) :
    identities.Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_all1; intro c
  have hh (ha : f y x = a) (hb : f x y = b) : f a b = c ↔ f y c = x := by
    have hi := E907.left_division h y x c
    change f y c = x ↔ c = f (f y x) (f x y) at hi
    rw [ha,hb] at hi
    exact eq_comm.trans hi.symm
  by_cases ha : f y x = a <;> by_cases hb : f x y = b <;>
    by_cases hc : f a b = c <;> by_cases hd : f y c = x <;>
    simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p]

omit [NeZero n] in
lemma model_shortTwo (f : Fin n → Fin n → Fin n) (h : Holds f) (a : Fin n) :
    (shortTwo a).Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro b
  split
  · rename_i hba
    apply sat_single
    have hh : ¬ (f a a = b ∧ f a b = a) := by
      rintro ⟨hab,hb⟩
      have hi := E907.pointed_period_two h a (by change f a (f a a) = a; rw [hab,hb])
      exact hba (hab.symm.trans hi)
    by_cases hab : f a a = b <;> simp_all [CNF.Clause.eval, meaning, p]
  · exact CNF.sat_empty

omit [NeZero n] in
lemma model_shortThree (f : Fin n → Fin n → Fin n) (h : Holds f) (a : Fin n) :
    (shortThree a).Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro b
  apply sat_all1; intro c
  split
  · rename_i hd
    apply sat_single
    have hh : ¬ (f a a = b ∧ f a b = c ∧ f a c = a) := by
      rintro ⟨hab,hbc,hca⟩
      have hi := E907.pointed_period_three h a (by
        change f a (f a (f a a)) = a; rw [hab,hbc,hca])
      exact hd.1 (hab.symm.trans hi)
    by_cases hab : f a a = b <;> by_cases hbc : f a b = c <;>
      simp_all [CNF.Clause.eval, meaning, p]
  · exact CNF.sat_empty

omit [NeZero n] in
lemma model_shortFour (f : Fin n → Fin n → Fin n) (h : Holds f) (a : Fin n) :
    (shortFour a).Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro b
  apply sat_all1; intro c
  apply sat_all1; intro d
  split
  · rename_i hd
    apply sat_single
    have hh : ¬ (f a a = b ∧ f a b = c ∧ f a c = d ∧ f a d = a) := by
      rintro ⟨hab,hbc,hcd,hda⟩
      have hi := E907.pointed_period_four h a (by
        change f a (f a (f a (f a a))) = a; rw [hab,hbc,hcd,hda])
      exact hd.1 (hab.symm.trans hi)
    by_cases hab : f a a = b <;> by_cases hbc : f a b = c <;>
      by_cases hcd : f a c = d <;> simp_all [CNF.Clause.eval, meaning, p]
  · exact CNF.sat_empty

omit [NeZero n] in
lemma model_cycles (f : Fin n → Fin n → Fin n) (h : Holds f) : cycles.Sat (meaning f) := by
  apply sat_all1; intro a
  exact sat_append _ _ _
    (sat_append _ _ _ (model_shortTwo f h a) (model_shortThree f h a))
    (model_shortFour f h a)

lemma model_formula (f : Fin n → Fin n → Fin n) (h : Holds f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    (formula n).Sat (meaning f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨model_latin f h, model_identities f h⟩, model_diagonal f hd⟩,
    model_chain f hc⟩, model_cycles f h⟩

def natFormula : CNF ℕ := sanitize ((formula 10).relabel code)

lemma no_model_of_unsat (hn : natFormula.Unsat) (f : Fin 10 → Fin 10 → Fin 10)
    (h : Holds f) (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : False := by
  have unsat_raw : ((formula 10).relabel code).Unsat := by
    intro a
    cases he : (((formula 10).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : natFormula.Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hn' (meaning f)
  rw [model_formula f h hd hc] at hh
  contradiction

theorem not_hasModel (hn : natFormula.Unsat) : ¬ Law907.HasModel 10 := by
  rintro ⟨M,hM⟩
  obtain ⟨f,hf,hd,hc⟩ := normalized M.op (Law907.models_iff.mp hM)
  exact no_model_of_unsat hn f hf hd hc
end Spectrum.E907.OrderTen.Encoding
