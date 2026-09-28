import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT

/-! A one-hot encoding of the normalized homogeneous E1516 conditions.
The soundness proof applies to arbitrary functions, independently of SAT search. -/
namespace Definability.Homogeneous1516.Encoding
open Std.Sat
abbrev K := ZMod 29
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
abbrev Atom := (K × K) ⊕ K
abbrev cell (x y : K) : Atom := .inl (x,y)
abbrev scalar (c : K) : Atom := .inr c

def meaning (f : K → K) (c : K) : Atom → Bool
  | .inl (x,y) => decide (f x = y)
  | .inr a => decide (c = a)

def elements : List K := (List.finRange 29).map (fun i => (i.val : K))
def all1 {α : Type} (F : K → CNF α) : CNF α :=
  ⟨elements.toArray.flatMap (fun x => (F x).clauses)⟩

@[simp] lemma mem_elements (x : K) : x ∈ elements := by
  apply List.mem_map.mpr
  exact ⟨⟨x.val, ZMod.val_lt x⟩, List.mem_finRange _, by simp⟩
lemma sat_all1 {α : Type} (a : α → Bool) (F : K → CNF α)
    (h : ∀ x, CNF.Sat a (F x)) : CNF.Sat a (all1 F) := by
  simp only [CNF.Sat, CNF.eval, all1, Array.all_flatMap, List.all_toArray, List.all_eq_true]
  exact fun x _ => h x
lemma sat_single {α : Type} (a : α → Bool) (c : CNF.Clause α)
    (h : CNF.Clause.eval a c = true) : CNF.Sat a ⟨#[c]⟩ := by
  simpa [CNF.Sat, CNF.eval] using h
lemma sat_append {α : Type} (a : α → Bool) (F G : CNF α)
    (hF : CNF.Sat a F) (hG : CNF.Sat a G) : CNF.Sat a (F ++ G) := by
  simp_all [CNF.Sat]

def rows : CNF Atom := all1 fun x =>
  ⟨#[elements.map (fun y => (cell x y, true))]⟩ ++
  all1 fun y => all1 fun z => if y.val < z.val then
    ⟨#[[(cell x y,false),(cell x z,false)]]⟩ else .empty
def columns : CNF Atom := all1 fun y =>
  ⟨#[elements.map (fun x => (cell x y, true))]⟩ ++
  all1 fun x => all1 fun z => if x.val < z.val then
    ⟨#[[(cell x y,false),(cell z y,false)]]⟩ else .empty
def scalars : CNF Atom :=
  ⟨#[elements.map (fun c => (scalar c,true)), [(scalar 0,false)]]⟩ ++
  all1 fun c => all1 fun d => if c.val < d.val then
    ⟨#[[(scalar c,false),(scalar d,false)]]⟩ else .empty
def fixed (s : K) : CNF Atom := ⟨#[[(cell 1 s,true)],[(cell 0 0,false)]]⟩
def zeroRight (s : K) : CNF Atom := all1 fun c => if c = 0 then .empty else
  ⟨#[[(scalar c,false),(cell (c*c/s) 0,true)]]⟩
def zeroLeft : CNF Atom := all1 fun c => if c = 0 then .empty else all1 fun u =>
  ⟨#[[(scalar c,false),(cell 0 u,false),(cell u c⁻¹,true)]]⟩
def mainLaw (s : K) : CNF Atom := all1 fun t => if t = 0 then .empty else
  all1 fun u => all1 fun v =>
    ⟨#[[(cell t u,false),(cell u v,false),(cell ((s*t)⁻¹*v) (s*t)⁻¹,true)]]⟩
def rightZero : CNF Atom := all1 fun t => if t = 0 then .empty else
  all1 fun c => if c = 0 then .empty else
    ⟨#[[(scalar c,false),(cell t (c*t),false)]]⟩
def rightUnique : CNF Atom := all1 fun t => if t = 0 then .empty else
  all1 fun u => if u ≠ 0 ∧ u.val < t.val then all1 fun a =>
    ⟨#[[(cell t a,false),(cell u (a*u/t),false)]]⟩ else .empty
def formula (s : K) : CNF Atom :=
  rows ++ columns ++ scalars ++ fixed s ++ zeroRight s ++ zeroLeft ++
  mainLaw s ++ rightZero ++ rightUnique

structure Conditions (f : K → K) (c s : K) : Prop where
  bijective : Function.Bijective f
  c_ne_zero : c ≠ 0
  f_zero_ne_zero : f 0 ≠ 0
  f_one : f 1 = s
  zero_right : f (c*c/s) = 0
  zero_left : f (f 0) = c⁻¹
  main : ∀ t, t ≠ 0 → f ((s*t)⁻¹*f (f t)) = (s*t)⁻¹
  right_zero : ∀ t, t ≠ 0 → f t / t ≠ c
  right_unique : ∀ t u, t ≠ 0 → u ≠ 0 → f t / t = f u / u → t = u

lemma model_rows (f : K → K) (c : K) : CNF.Sat (meaning f c) rows := by
  apply sat_all1; intro x
  apply sat_append
  · apply sat_single
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨f x, mem_elements _, by simp [meaning, cell]⟩
  · apply sat_all1; intro y
    apply sat_all1; intro z
    split
    · rename_i hyz
      apply sat_single
      have hn : y ≠ z := by intro h; subst z; omega
      by_cases h : f x = y <;> simp_all [CNF.Clause.eval, meaning, cell]
    · exact CNF.sat_empty

lemma model_columns (f : K → K) (c : K) (hf : Function.Bijective f) :
    CNF.Sat (meaning f c) columns := by
  apply sat_all1; intro y
  apply sat_append
  · obtain ⟨x,hx⟩ := hf.2 y
    apply sat_single
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨x, mem_elements _, by simp [meaning, cell, hx]⟩
  · apply sat_all1; intro x
    apply sat_all1; intro z
    split
    · rename_i hxz
      apply sat_single
      by_cases h : f x = y
      · have hn : f z ≠ y := by
          intro hz
          have he := hf.1 (h.trans hz.symm)
          subst z
          omega
        simp [CNF.Clause.eval, meaning, cell, hn]
      · simp [CNF.Clause.eval, meaning, cell, h]
    · exact CNF.sat_empty

lemma model_scalars (f : K → K) (c : K) (hc : c ≠ 0) :
    CNF.Sat (meaning f c) scalars := by
  apply sat_append
  · have hh : CNF.Clause.eval (meaning f c) (elements.map (fun d => (scalar d,true))) = true := by
      simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
      exact ⟨c, mem_elements _, by simp [meaning, scalar]⟩
    simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, scalar, hc]
  · apply sat_all1; intro a
    apply sat_all1; intro b
    split
    · rename_i hab
      apply sat_single
      have hn : a ≠ b := by intro he; subst b; omega
      by_cases h : c = a <;> simp_all [CNF.Clause.eval, meaning, scalar]
    · exact CNF.sat_empty

lemma model_formula (f : K → K) (c s : K) (h : Conditions f c s) :
    CNF.Sat (meaning f c) (formula s) := by
  have hfixed : CNF.Sat (meaning f c) (fixed s) := by
    simp [fixed, CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, cell, h.f_one, h.f_zero_ne_zero]
  have hzr : CNF.Sat (meaning f c) (zeroRight s) := by
    apply sat_all1; intro d
    split
    · exact CNF.sat_empty
    · apply sat_single
      by_cases hd : c = d
      · subst d; simp [CNF.Clause.eval, meaning, scalar, cell, h.zero_right]
      · simp [CNF.Clause.eval, meaning, scalar, cell, hd]
  have hzl : CNF.Sat (meaning f c) zeroLeft := by
    apply sat_all1; intro d
    split
    · exact CNF.sat_empty
    · apply sat_all1; intro u
      apply sat_single
      by_cases hd : c = d
      · subst d
        by_cases hu : f 0 = u
        · have hh : f u = c⁻¹ := hu ▸ h.zero_left
          simp [CNF.Clause.eval, meaning, scalar, cell, hh]
        · simp [CNF.Clause.eval, meaning, scalar, cell, hu]
      · simp [CNF.Clause.eval, meaning, scalar, cell, hd]
  have hmain : CNF.Sat (meaning f c) (mainLaw s) := by
    apply sat_all1; intro t
    split
    · exact CNF.sat_empty
    · rename_i ht
      apply sat_all1; intro u
      apply sat_all1; intro v
      apply sat_single
      by_cases hu : f t = u
      · by_cases hv : f u = v
        · have hh : f ((s*t)⁻¹*v) = (s*t)⁻¹ := by simpa only [hu,hv] using h.main t ht
          simp only [mul_inv_rev] at hh
          simp [CNF.Clause.eval, meaning, cell, hh]
        · simp [CNF.Clause.eval, meaning, cell, hv]
      · simp [CNF.Clause.eval, meaning, cell, hu]
  have hrz : CNF.Sat (meaning f c) rightZero := by
    apply sat_all1; intro t
    split
    · exact CNF.sat_empty
    · rename_i ht
      apply sat_all1; intro d
      split
      · exact CNF.sat_empty
      · apply sat_single
        by_cases hd : c = d
        · subst d
          have hh : f t ≠ c*t := by
            intro he
            apply h.right_zero t ht
            rw [he, mul_div_cancel_right₀ _ ht]
          simp [CNF.Clause.eval, meaning, scalar, cell, hh]
        · simp [CNF.Clause.eval, meaning, scalar, cell, hd]
  have hru : CNF.Sat (meaning f c) rightUnique := by
    apply sat_all1; intro t
    split
    · exact CNF.sat_empty
    · rename_i ht
      apply sat_all1; intro u
      split
      · rename_i hu
        apply sat_all1; intro a
        apply sat_single
        by_cases ha : f t = a
        · have hh : f u ≠ a*u/t := by
            intro he
            have eq : f t/t = f u/u := by rw [ha,he]; field_simp [ht,hu.1] <;> ring
            have htu := h.right_unique t u ht hu.1 eq
            subst u
            exact (lt_irrefl _ hu.2)
          simp [CNF.Clause.eval, meaning, cell, hh]
        · simp [CNF.Clause.eval, meaning, cell, ha]
      · exact CNF.sat_empty
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨model_rows f c, model_columns f c h.bijective⟩,
    model_scalars f c h.c_ne_zero⟩, hfixed⟩, hzr⟩, hzl⟩, hmain⟩, hrz⟩, hru⟩

def code : Atom → Nat
  | .inl (x,y) => 29*x.val+y.val
  | .inr c => 841+c.val
def sanitize (F : CNF Nat) : CNF Nat :=
  ⟨F.clauses.filter (fun c => !(c.any (fun l => c.contains (l.1, !l.2))))⟩
def natFormula (s : K) : CNF Nat := sanitize ((formula s).relabel code)

lemma code_injective : Function.Injective code := by
  intro a b he
  rcases a with ⟨x,y⟩ | c <;> rcases b with ⟨z,w⟩ | d
  · have hx := ZMod.val_lt x
    have hy := ZMod.val_lt y
    have hz := ZMod.val_lt z
    have hw := ZMod.val_lt w
    simp only [code] at he
    have h1 : x.val = z.val := by omega
    have h2 : y.val = w.val := by omega
    rw [ZMod.val_injective 29 h1, ZMod.val_injective 29 h2]
  · have hx := ZMod.val_lt x
    have hy := ZMod.val_lt y
    simp only [code] at he
    omega
  · have hz := ZMod.val_lt z
    have hw := ZMod.val_lt w
    simp only [code] at he
    omega
  · simp only [code, Nat.add_left_cancel_iff] at he
    rw [ZMod.val_injective 29 he]

lemma no_conditions (s : K) (hn : (natFormula s).Unsat)
    (f : K → K) (c : K) (h : Conditions f c s) : False := by
  have hrel : ((formula s).relabel code).Unsat := by
    intro a
    cases he : ((formula s).relabel code).eval a with
    | false => rfl
    | true =>
      have hh : (natFormula s).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at *
        intro cl hc
        exact he cl (Array.mem_filter.mp hc).1
      have hfalse := hn a
      rw [hh] at hfalse
      contradiction
  have hf : (formula s).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp hrel
  have hh := hf (meaning f c)
  rw [model_formula f c s h] at hh
  contradiction

end Definability.Homogeneous1516.Encoding
