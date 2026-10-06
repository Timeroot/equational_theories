import equational_theories.Spectrum.SmallPairs.Encoding
import equational_theories.Spectrum.Equation667ConstantDiagonal

/-! A Latin-table encoding for E667 with a right identity labelled zero.
The extra propagation clauses are proved consequences of E667. In particular
there is no conditional assertion that an idempotent zero makes all elements
idempotent: this would be an invalid normalization for a prescribed identity. -/
namespace Spectrum.E667.RightIdentityTwelve
open Std.Sat
open E63.OrderTen.Encoding (all1 exactlyOne sat_all1 sat_single sat_append sat_exactlyOne sanitize)
open SmallPairs.Encoding (Atom p q code code_injective)
variable {n : ℕ} [NeZero n]

def Holds (f : Fin n → Fin n → Fin n) : Prop :=
  ∀ x y, f y (f x (f (f x x) y)) = x

def meaning (f : Fin n → Fin n → Fin n) (a : Atom n) : Bool :=
  if a.1 = 0 then decide (f a.2.1 a.2.2.1 = a.2.2.2)
  else decide (f (f a.2.1 a.2.1) a.2.2.1 = a.2.2.2)

def latin : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => p x y z) ++ exactlyOne (fun z => p x z y) ++
    exactlyOne (fun z => p z x y)
def inner (x y : Fin n) : CNF (Atom n) := all1 fun a => all1 fun b =>
  ⟨#[[(p x x a,false), (p a y b,false), (q x y b,true)],
     [(p x x a,false), (p a y b,true), (q x y b,false)]]⟩
def outer (x y : Fin n) : CNF (Atom n) := all1 fun a => all1 fun b =>
  ⟨#[[(q x y a,false), (p x a b,false), (p y b x,true)],
     [(q x y a,false), (p x a b,true), (p y b x,false)]]⟩
def identities : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => q x y z) ++ inner x y ++ outer x y

def chain : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + 1 < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty
def unit : CNF (Atom n) := all1 fun x => ⟨#[[(p x 0 x,true)]]⟩
def middleLatin : CNF (Atom n) := all1 fun x => all1 fun z =>
  exactlyOne (fun y => q x y z)
def nonconstant : CNF (Atom n) := all1 fun z =>
  ⟨#[(List.finRange n).map (fun x => (p x x z,false))]⟩
def threeCycles : CNF (Atom n) := all1 fun x => all1 fun a => all1 fun b =>
  ⟨#[[(p x x a,false),(p x a b,false),(p x b x,false),(p x x x,true)]]⟩
def twoCycles : CNF (Atom n) := all1 fun x => all1 fun a =>
  ⟨#[[(p x x a,false),(p x a x,false),(p a a a,true)]]⟩
def fibers : CNF (Atom n) := all1 fun e => all1 fun x => all1 fun y =>
  ⟨#[[(p e e e,false),(p x x e,false),(p e x y,false),(p e y x,true)],
     [(p e e e,false),(p e x y,false),(p e y x,false),(p x x e,true)],
     [(p e e e,false),(p x x e,false),(p e x y,false),(p y y e,true)]]⟩

def formula (n : ℕ) [NeZero n] : CNF (Atom n) :=
  latin ++ identities ++ chain ++ unit ++ middleLatin ++ nonconstant ++
    threeCycles ++ twoCycles ++ fibers

omit [NeZero n] in
theorem left_bijective {f : Fin n → Fin n → Fin n} (h : Holds f) (x : Fin n) :
    Function.Bijective (f x) := by
  have hs : Function.Surjective (f x) := fun y => ⟨f y (f (f y y) x), h y x⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

omit [NeZero n] in
theorem right_bijective {f : Fin n → Fin n → Fin n} (h : Holds f) (x : Fin n) :
    Function.Bijective (fun y => f y x) := by
  letI : Magma (Fin n) := ⟨f⟩
  have hi := E667883.right_injective667 (fun a b => (h a b).symm) x
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

omit [NeZero n] in
theorem model_latin (f : Fin n → Fin n → Fin n) (h : Holds f) :
    latin.Sat (meaning f) := by
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
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := (right_bijective h x).2 y
      exact ⟨z, by simp [meaning, hz]⟩
    · intro z w hz hw
      simp only [meaning, ↓reduceIte, decide_eq_true_eq] at hz hw
      exact (right_bijective h x).1 (hz.trans hw.symm)

omit [NeZero n] in
theorem model_inner (f : Fin n → Fin n → Fin n) (x y : Fin n) :
    (inner x y).Sat (meaning f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  by_cases ha : f x x = a
  · by_cases hb : f a y = b <;>
      simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]
  · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha]

omit [NeZero n] in
theorem model_outer (f : Fin n → Fin n → Fin n) (h : Holds f) (x y : Fin n) :
    (outer x y).Sat (meaning f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  by_cases ha : f (f x x) y = a
  · have he := h x y
    rw [ha] at he
    have hh : f x a = b ↔ f y b = x := by
      constructor
      · intro hb; rwa [hb] at he
      · intro hb; exact (left_bijective h y).1 (he.trans hb.symm)
    by_cases hb : f y b = x <;>
      simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q]
  · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, q, ha]

omit [NeZero n] in
theorem model_identities (f : Fin n → Fin n → Fin n) (h : Holds f) :
    identities.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨f (f x x) y, by simp [meaning]⟩
      · intro z w hz hw
        simp [meaning] at hz hw
        exact hz.symm.trans hw
    · exact model_inner f x y
  · exact model_outer f h x y

theorem model_chain (f : Fin n → Fin n → Fin n)
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

theorem model_unit (f : Fin n → Fin n → Fin n) (h : ∀ x, f x 0 = x) :
    unit.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_single
  simp [CNF.Clause.eval, meaning, p, h]

omit [NeZero n] in
theorem model_middleLatin (f : Fin n → Fin n → Fin n) (h : Holds f) :
    middleLatin.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro z
  apply sat_exactlyOne
  · obtain ⟨y, hy⟩ := (left_bijective h (f x x)).2 z
    exact ⟨y, by simp [meaning, hy]⟩
  · intro y w hy hw
    simp [meaning] at hy hw
    exact (left_bijective h (f x x)).1 (hy.trans hw.symm)

omit [NeZero n] in
theorem model_nonconstant (f : Fin n → Fin n → Fin n) (h : Holds f) (hd : 3 ∣ n) :
    nonconstant.Sat (meaning f) := by
  classical
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro z
  apply sat_single
  have hh := ConstantDiagonal.not_constant_of_three_dvd
    (fun x y => (h x y).symm) z (by simpa using hd)
  push Not at hh
  obtain ⟨x, hx⟩ := hh
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨x, List.mem_finRange _, by simpa [meaning, p] using hx⟩

omit [NeZero n] in
theorem model_threeCycles (f : Fin n → Fin n → Fin n) (h : Holds f) :
    threeCycles.Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_single
  have hh (h1 : f x x = a) (h2 : f x a = b) (h3 : f x b = x) : f x x = x :=
    three_cycle_implies_idempotent (fun x y => (h x y).symm) x
      (by change f x (f x (f x x)) = x; rw [h1, h2, h3])
  by_cases h1 : f x x = a <;> by_cases h2 : f x a = b <;> by_cases h3 : f x b = x <;>
    simp_all [CNF.Clause.eval, meaning, p]

omit [NeZero n] in
theorem model_twoCycles (f : Fin n → Fin n → Fin n) (h : Holds f) :
    twoCycles.Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_single
  have hh (h1 : f x x = a) (h2 : f x a = x) : f a a = a := by
    have ht := two_cycle_square_idempotent (fun x y => (h x y).symm) x
      (by change f x (f x x) = x; rw [h1, h2])
    simpa only [show x ◇ x = a from h1] using ht
  by_cases h1 : f x x = a <;> by_cases h2 : f x a = x <;>
    simp_all [CNF.Clause.eval, meaning, p]

omit [NeZero n] in
theorem model_fibers (f : Fin n → Fin n → Fin n) (h : Holds f) :
    fibers.Sat (meaning f) := by
  letI : Magma (Fin n) := ⟨f⟩
  apply sat_all1; intro e
  apply sat_all1; intro x
  apply sat_all1; intro y
  have h1 (he : f e e = e) (hs : f x x = e) (hy : f e x = y) : f e y = x := by
    have ht := (square_fiber_iff (fun x y => (h x y).symm) e he x).mp hs
    simpa only [show e ◇ x = y from hy] using ht
  have h2 (he : f e e = e) (hy : f e x = y) (hz : f e y = x) : f x x = e :=
    (square_fiber_iff (fun x y => (h x y).symm) e he x).mpr
      (by change f e (f e x) = x; rw [hy, hz])
  have h3 (he : f e e = e) (hs : f x x = e) (hy : f e x = y) : f y y = e := by
    have ht := square_fiber_invariant (fun x y => (h x y).symm) e he x hs
    simpa only [show e ◇ x = y from hy] using ht
  by_cases he : f e e = e <;> by_cases hs : f x x = e <;>
    by_cases hy : f e x = y <;> by_cases hz : f e y = x <;>
      simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p]

theorem model_formula (f : Fin n → Fin n → Fin n) (h : Holds f) (hd : 3 ∣ n)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) (hu : ∀ x, f x 0 = x) :
    (formula n).Sat (meaning f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨model_latin f h, model_identities f h⟩, model_chain f hc⟩,
    model_unit f hu⟩, model_middleLatin f h⟩, model_nonconstant f h hd⟩,
    model_threeCycles f h⟩, model_twoCycles f h⟩, model_fibers f h⟩

def natFormula (n : ℕ) [NeZero n] : CNF ℕ := sanitize ((formula n).relabel code)

theorem no_normalized_model (hn : (natFormula n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds f) (hd : 3 ∣ n)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) (hu : ∀ x, f x 0 = x) : False := by
  have raw : ((formula n).relabel code).Unsat := by
    intro a
    cases he : ((formula n).relabel code).eval a with
    | false => rfl
    | true =>
      have hs : (natFormula n).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hh := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp raw (meaning f)
  rw [model_formula f h hd hc hu] at hh
  contradiction

omit [NeZero n] in
theorem holds_relabel {f : Fin n → Fin n → Fin n} (h : Holds f)
    (e : Fin n ≃ Fin n) : Holds (fun x y => e (f (e.symm x) (e.symm y))) := by
  intro x y
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
    congrArg e (h (e.symm x) (e.symm y))

/-- First move the right identity to zero, then chain-label its left
translation with a permutation fixing zero. Neither step assumes idempotency
of any other element. -/
theorem no_right_identity (hn : (natFormula n).Unsat) (hd : 3 ∣ n)
    (f : Fin n → Fin n → Fin n) (h : Holds f) (u : Fin n)
    (hu : ∀ x, f x u = x) : False := by
  classical
  let s := Equiv.swap u (0 : Fin n)
  let g (x y : Fin n) := s (f (s.symm x) (s.symm y))
  have hg : Holds g := holds_relabel h s
  have gu (x : Fin n) : g x 0 = x := by
    have hs : s.symm 0 = u := Equiv.swap_apply_right u 0
    simp only [g, hs, hu, Equiv.apply_symm_apply]
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let q (x y : Fin n) := e (g (e.symm x) (e.symm y))
  apply no_normalized_model hn q (holds_relabel hg e) hd
  · intro y
    simpa only [q, he'] using hc y
  · intro x
    simp only [q, he', gu, Equiv.apply_symm_apply]

end Spectrum.E667.RightIdentityTwelve
