import equational_theories.Spectrum.Equation63.OrderTen.Normalization
import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT

/-!
# A transparent one-hot encoding

The atom `(x,y,z)` means `x*y=z`. The clauses assert that the table is Latin,
the cubic law (with redundant cancellation consequences), the two translation
lemmas, and the symmetry rules proved in `Normalization`. This file proves
that every normalized model satisfies every clause; it uses no SAT solver.
-/
namespace Spectrum.E63.OrderTen.Encoding
open Std.Sat
variable {n : ℕ} [NeZero n]
abbrev Atom (n : ℕ) := Fin n × Fin n × Fin n
abbrev p (x y z : Fin n) : Atom n := (x,y,z)
def meaning (f : Fin n → Fin n → Fin n) (a : Atom n) : Bool :=
  decide (f a.1 a.2.1 = a.2.2)

def all1 {α : Type} (F : Fin n → CNF α) : CNF α :=
  ⟨(List.finRange n).toArray.flatMap (fun x => (F x).clauses)⟩
omit [NeZero n] in
lemma sat_all1 {α : Type} (m : α → Bool) (F : Fin n → CNF α)
    (h : ∀ x, (F x).Sat m) : (all1 F).Sat m := by
  simp only [CNF.Sat, CNF.eval, all1, Array.all_flatMap, List.all_toArray, List.all_eq_true]
  exact fun x _ => h x
lemma sat_single {α : Type} (m : α → Bool) (c : CNF.Clause α)
    (h : CNF.Clause.eval m c = true) : CNF.Sat m ⟨#[c]⟩ := by
  simpa [CNF.Sat, CNF.eval] using h
lemma sat_append {α : Type} (m : α → Bool) (F G : CNF α)
    (hF : F.Sat m) (hG : G.Sat m) : (F ++ G).Sat m := by
  simp_all [CNF.Sat]

def exactlyOne {α : Type} (v : Fin n → α) : CNF α :=
  ⟨#[(List.finRange n).map (fun z => (v z, true))]⟩ ++
  all1 fun z => all1 fun w => if z.val < w.val then
    ⟨#[[(v z,false),(v w,false)]]⟩ else .empty

omit [NeZero n] in
lemma sat_exactlyOne {α : Type} (m : α → Bool) (v : Fin n → α)
    (he : ∃ z, m (v z) = true)
    (hu : ∀ z w, m (v z) = true → m (v w) = true → z = w) :
    (exactlyOne v).Sat m := by
  apply sat_append
  · apply sat_single
    obtain ⟨z,hz⟩ := he
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨z, List.mem_finRange _, by simpa using hz⟩
  · apply sat_all1; intro z
    apply sat_all1; intro w
    split
    · rename_i hzw
      apply sat_single
      by_cases hz : m (v z) = true
      · have hw : m (v w) = false := by
          cases hh : m (v w)
          · rfl
          · have := congrArg Fin.val (hu z w hz hh)
            omega
        simp [CNF.Clause.eval, hw]
      · simp_all [CNF.Clause.eval]
    · exact CNF.sat_empty

def latin : CNF (Atom n) := all1 fun x => all1 fun y =>
  exactlyOne (fun z => p x y z) ++ exactlyOne (fun z => p x z y) ++
    exactlyOne (fun z => p z x y)

def cubic : CNF (Atom n) := all1 fun y => all1 fun x => all1 fun a => all1 fun b =>
  ⟨#[[(p y x a,false),(p y a b,false),(p b y x,true)],
     [(p y x a,false),(p y a b,true),(p b y x,false)],
     [(p y x a,true),(p y a b,false),(p b y x,false)]]⟩

def cycles : CNF (Atom n) := all1 fun x => all1 fun y => all1 fun z =>
  ⟨#[[(p x x y,false),(p x y z,false),(p x z x,true)]]⟩ ++
  if y = z then .empty else ⟨#[[(p x y z,false),(p x z y,false)]]⟩

def diagonal : CNF (Atom n) := all1 fun x =>
  ⟨#[[(p 0 0 0,false),(p x x x,true)]]⟩
def chain : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + 1 < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty

def formula (n : ℕ) [NeZero n] : CNF (Atom n) :=
  latin ++ cubic ++ cycles ++ diagonal ++ chain

omit [NeZero n] in
lemma model_latin (f : Fin n → Fin n → Fin n) (h : Cubic f) : latin.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨f x y, by simp [meaning]⟩
      · intro z w hz hw
        simp only [meaning, decide_eq_true_eq] at hz hw
        exact hz.symm.trans hw
    · apply sat_exactlyOne
      · obtain ⟨z,hz⟩ := Finite.injective_iff_surjective.mp (left_injective h x) y
        exact ⟨z, by simp [meaning, hz]⟩
      · intro z w hz hw
        simp only [meaning, decide_eq_true_eq] at hz hw
        exact left_injective h x (hz.trans hw.symm)
  · apply sat_exactlyOne
    · exact ⟨f x (f x y), by simp [meaning, h]⟩
    · intro z w hz hw
      simp only [meaning, decide_eq_true_eq] at hz hw
      exact right_injective h x (hz.trans hw.symm)

omit [NeZero n] in
lemma model_cubic (f : Fin n → Fin n → Fin n) (h : Cubic f) : cubic.Sat (meaning f) := by
  apply sat_all1; intro y
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  have hab (ha : f y x = a) (hb : f y a = b) : f b y = x := by
    simpa only [ha, hb] using h y x
  have hac (ha : f y x = a) (hc : f b y = x) : f y a = b := by
    apply right_injective h y
    simpa only [ha, hc] using h y x
  have hbc (hb : f y a = b) (hc : f b y = x) : f y x = a := by
    apply left_injective h y
    apply right_injective h y
    simpa only [hb, hc] using h y x
  by_cases ha : f y x = a <;> by_cases hb : f y a = b <;> by_cases hc : f b y = x <;>
    simp_all [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p]

omit [NeZero n] in
lemma model_cycles (f : Fin n → Fin n → Fin n) (h : Cubic f) : cycles.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro z
  apply sat_append
  · apply sat_single
    have hh (hy : f x x = y) (hz : f x y = z) : f x z = x := by
      simpa only [hy, hz] using own_cube h x
    by_cases hy : f x x = y <;> by_cases hz : f x y = z <;>
      simp_all [CNF.Clause.eval, meaning, p]
  · split
    · exact CNF.sat_empty
    · rename_i hyz
      apply sat_single
      have hh : ¬ (f x y = z ∧ f x z = y) := fun ⟨hy,hz⟩ => hyz (no_two_cycle h x y z hy hz)
      by_cases hy : f x y = z <;> simp_all [CNF.Clause.eval, meaning, p]

lemma model_diagonal (f : Fin n → Fin n → Fin n) (h : f 0 0 = 0 → ∀ x, f x x = x) :
    diagonal.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_single
  by_cases h0 : f 0 0 = 0 <;> simp_all [CNF.Clause.eval, meaning, p]

lemma model_chain (f : Fin n → Fin n → Fin n) (h : ∀ y, (f 0 y).val ≤ y.val + 1) :
    chain.Sat (meaning f) := by
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

lemma model_formula (f : Fin n → Fin n → Fin n) (h : Cubic f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    (formula n).Sat (meaning f) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨model_latin f h, model_cubic f h⟩, model_cycles f h⟩,
    model_diagonal f hd⟩, model_chain f hc⟩

/-- DIMACS numbers atoms from 1; Lean's CNF representation numbers from 0. -/
def code (a : Atom n) : ℕ := (a.1.val * n + a.2.1.val) * n + a.2.2.val

lemma code_injective : Function.Injective (@code 10) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ he
  dsimp [code] at he
  have hz : z = z' := Fin.ext (by omega)
  have hy : y = y' := Fin.ext (by omega)
  have hx : x = x' := Fin.ext (by omega)
  exact Prod.ext hx (Prod.ext hy hz)

/-- Remove tautologies before numbering clauses, as Lean's LRAT conversion does. -/
def sanitize (F : CNF ℕ) : CNF ℕ :=
  ⟨F.clauses.filter (fun c => !(c.any (fun l => c.contains (l.1, !l.2))))⟩
def natFormula : CNF ℕ := sanitize ((formula 10).relabel code)

lemma no_model_of_unsat (hn : natFormula.Unsat) (f : Fin 10 → Fin 10 → Fin 10)
    (h : Cubic f) (hd : f 0 0 = 0 → ∀ x, f x x = x)
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

end Spectrum.E63.OrderTen.Encoding
