import equational_theories.Spectrum.SmallPairs.Basic
import equational_theories.Spectrum.Equation63.OrderTen.Encoding

/-!
Each case uses just two kinds of atoms: `p x y z` means `f x y = z`, and
`q x y z` records the middle subterm. The outermost left translation is
eliminated by cancellation. All clauses below have mathematical soundness
proofs; the external solver only supplies LRAT data for this fixed encoding.
-/
namespace Spectrum.SmallPairs.Encoding
open Std.Sat
open E63.OrderTen.Encoding (all1 exactlyOne sat_all1 sat_single sat_append sat_exactlyOne sanitize)

variable {n : ℕ} [NeZero n]
abbrev Atom (n : ℕ) := Fin 2 × Fin n × Fin n × Fin n
abbrev p (x y z : Fin n) : Atom n := (0,x,y,z)
abbrev q (x y z : Fin n) : Atom n := (1,x,y,z)

def meaning (k : Kind) (f : Fin n → Fin n → Fin n) (a : Atom n) : Bool :=
  if a.1 = 0 then decide (f a.2.1 a.2.2.1 = a.2.2.2)
  else decide (middle k f a.2.1 a.2.2.1 = a.2.2.2)

def latin (k : Kind) : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => p x y z) ++ exactlyOne (fun z => p x z y) ++
    if k = .e704 ∨ k = .e1279 ∨ k = .e1313 then exactlyOne (fun z => p z x y) else .empty

def inner (k : Kind) (x y : Fin n) : CNF (Atom n) := all1 fun a => all1 fun b =>
  ⟨#[[(p (first k x y).1 (first k x y).2 a,false), (p a (right k x y) b,false), (q x y b,true)],
     [(p (first k x y).1 (first k x y).2 a,false), (p a (right k x y) b,true), (q x y b,false)]]⟩

def outer (k : Kind) (x y : Fin n) : CNF (Atom n) := all1 fun a => all1 fun b =>
  ⟨#[[(q x y a,false), (p (last k x y a).1 (last k x y a).2 b,false), (p y b x,true)],
     [(q x y a,false), (p (last k x y a).1 (last k x y a).2 b,true), (p y b x,false)]]⟩

def identities (k : Kind) : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => q x y z) ++ inner k x y ++ outer k x y

def diagonal : CNF (Atom n) := all1 fun x => ⟨#[[(p 0 0 0,false),(p x x x,true)]]⟩
def chain : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + 1 < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty
def squares (k : Kind) : CNF (Atom n) :=
  if k = .e704 ∨ k = .e1279 then all1 fun y => exactlyOne (fun x => p x x y) else .empty

def formula (k : Kind) (n : ℕ) [NeZero n] : CNF (Atom n) :=
  latin k ++ identities k ++ diagonal ++ chain ++ squares k

omit [NeZero n] in
lemma model_latin (k : Kind) (f : Fin n → Fin n → Fin n) (h : Holds k f) :
    (latin k).Sat (meaning k f) := by
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
      · obtain ⟨z,hz⟩ := (left_bijective h x).2 y
        exact ⟨z, by simp [meaning, hz]⟩
      · intro z w hz hw
        simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
        exact (left_bijective h x).1 (hz.trans hw.symm)
  · split
    · rename_i hk
      apply sat_exactlyOne
      · obtain ⟨z,hz⟩ := (right_bijective_of_kind h hk x).2 y
        exact ⟨z, by simp [meaning, hz]⟩
      · intro z w hz hw
        simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
        exact (right_bijective_of_kind h hk x).1 (hz.trans hw.symm)
    · exact CNF.sat_empty

omit [NeZero n] in
lemma model_inner (k : Kind) (f : Fin n → Fin n → Fin n) (x y : Fin n) :
    (inner k x y).Sat (meaning k f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  by_cases ha : f (first k x y).1 (first k x y).2 = a
  · have hh : middle k f x y = b ↔ f a (right k x y) = b := by rw [middle, ha]
    by_cases hb : f a (right k x y) = b <;>
      simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]
  · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha]

omit [NeZero n] in
lemma model_outer (k : Kind) (f : Fin n → Fin n → Fin n) (h : Holds k f) (x y : Fin n) :
    (outer k x y).Sat (meaning k f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  by_cases ha : middle k f x y = a
  · have he := h x y
    rw [ha] at he
    have hh : f (last k x y a).1 (last k x y a).2 = b ↔ f y b = x := by
      constructor
      · intro hb; rwa [hb] at he
      · intro hb; exact (left_bijective h y).1 (he.trans hb.symm)
    by_cases hb : f y b = x <;>
      simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]
  · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha]

omit [NeZero n] in
lemma model_identities (k : Kind) (f : Fin n → Fin n → Fin n) (h : Holds k f) :
    (identities k).Sat (meaning k f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨middle k f x y, by simp [meaning]⟩
      · intro z w hz hw
        simp [meaning] at hz hw
        exact hz.symm.trans hw
    · exact model_inner k f x y
  · exact model_outer k f h x y

lemma model_diagonal (k : Kind) (f : Fin n → Fin n → Fin n)
    (h : f 0 0 = 0 → ∀ x, f x x = x) : diagonal.Sat (meaning k f) := by
  apply sat_all1; intro x
  apply sat_single
  by_cases h0 : f 0 0 = 0 <;> simp_all [CNF.Clause.eval, meaning, p]

lemma model_chain (k : Kind) (f : Fin n → Fin n → Fin n)
    (h : ∀ y, (f 0 y).val ≤ y.val + 1) : chain.Sat (meaning k f) := by
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
lemma model_squares (k : Kind) (f : Fin n → Fin n → Fin n) (h : Holds k f) :
    (squares k).Sat (meaning k f) := by
  unfold squares
  split
  · rename_i hk
    apply sat_all1; intro y
    apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := (square_bijective h hk).2 y
      exact ⟨z, by simp [meaning, hz]⟩
    · intro z w hz hw
      simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
      exact (square_bijective h hk).1 (hz.trans hw.symm)
  · exact CNF.sat_empty

lemma model_formula (k : Kind) (f : Fin n → Fin n → Fin n) (h : Holds k f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    (formula k n).Sat (meaning k f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨model_latin k f h, model_identities k f h⟩, model_diagonal k f hd⟩,
    model_chain k f hc⟩, model_squares k f h⟩

def code (a : Atom n) : ℕ := ((a.1.val * n + a.2.1.val) * n + a.2.2.1.val) * n + a.2.2.2.val

lemma code_injective : Function.Injective (@code n) := by
  have digits {a b c d : ℕ} (hc : c < n) (hd : d < n) (he : a*n+c = b*n+d) :
      a = b ∧ c = d := by
    have ht := congrArg (fun t => t % n) he
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at ht
    exact ⟨Nat.eq_of_mul_eq_mul_right (NeZero.pos n) (by omega), ht⟩
  rintro ⟨t,x,y,z⟩ ⟨t',x',y',z'⟩ he
  obtain ⟨he,hz⟩ := digits z.isLt z'.isLt he
  obtain ⟨he,hy⟩ := digits y.isLt y'.isLt he
  obtain ⟨ht,hx⟩ := digits x.isLt x'.isLt he
  exact Prod.ext (Fin.ext ht) (Prod.ext (Fin.ext hx) (Prod.ext (Fin.ext hy) (Fin.ext hz)))

def natFormula (k : Kind) (n : ℕ) [NeZero n] : CNF ℕ :=
  sanitize ((formula k n).relabel code)

lemma no_model_of_unsat (k : Kind) (hn : (natFormula k n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds k f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : False := by
  have unsat_raw : ((formula k n).relabel code).Unsat := by
    intro a
    cases he : (((formula k n).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula k n).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hn' (meaning k f)
  rw [model_formula k f h hd hc] at hh
  contradiction

theorem not_hasModel (k : Kind) (hn : (natFormula k n).Unsat) : ¬ k.law.HasModel n := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf, hd, hc⟩ := normalized M.op ((holds_iff k M).mpr hM)
  exact no_model_of_unsat k hn f hf hd hc

end Spectrum.SmallPairs.Encoding
