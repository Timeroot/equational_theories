import equational_theories.Spectrum.Equation667Twelve.CollisionConsequences
import equational_theories.Spectrum.Equation667Twelve.RowMoves

/-! Smaller refutations for the expensive prescribed-row cases. They use a
previously proved restriction on square collisions and, for two rows, the
minimum possible value of one entry under row-preserving relabellings. -/
set_option maxRecDepth 65536
namespace Spectrum.E667.Twelve.RowReduction
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open SmallPairs.Encoding (Atom p code code_injective)
open RightIdentityTwelve (Holds meaning)
open Spectrum.FiniteSearch
open FixedSquare.Cases (table)

def Minimal (i : Fin 77) (f : Fin 12 → Fin 12 → Fin 12) : Prop :=
  ∀ s : Equiv.Perm (Fin 12), s 0 = 0 →
    (∀ x, s (table i x) = table i (s x)) → f 1 2 ≤ relabel f s 1 2

/-- A finite orbit has a minimum. Only the single entry `(1,2)` is minimized;
no assumptions about the outputs or the other moving inputs are needed. -/
theorem exists_minimal (i : Fin 77) (f : Fin 12 → Fin 12 → Fin 12)
    (h : Holds f) (hr : ∀ y, f 0 y = table i y) :
    ∃ g : Fin 12 → Fin 12 → Fin 12, Holds g ∧ (∀ y, g 0 y = table i y) ∧ Minimal i g := by
  classical
  let S : Finset (Equiv.Perm (Fin 12)) := Finset.univ.filter
    (fun e => e 0 = 0 ∧ ∀ x, e (table i x) = table i (e x))
  let key (e : Equiv.Perm (Fin 12)) := relabel f e 1 2
  obtain ⟨e, he, hmin⟩ := S.exists_min_image key ⟨Equiv.refl _, by simp [S]⟩
  have he' := (Finset.mem_filter.mp he).2
  have he0 : e.symm 0 = 0 := by
    apply e.injective
    rw [Equiv.apply_symm_apply, he'.1]
  refine ⟨relabel f e, RightIdentityTwelve.holds_relabel h e, ?_, ?_⟩
  · intro y
    simp only [relabel,he0,hr,he'.2,Equiv.apply_symm_apply]
  · intro s hs0 hs
    have hnew : e.trans s ∈ S := by
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · simp only [Equiv.trans_apply,he'.1,hs0]
      · intro x
        simp only [Equiv.trans_apply,he'.2,hs]
    exact hmin (e.trans s) hnew

def minMove (m : Move) : CNF (Atom 12) :=
  all1 fun z => all1 fun w =>
    if forward m w < z then
      ⟨#[[(p 1 2 z,false),(p (backward m 1) (backward m 2) w,false)]]⟩
    else .empty

def minimumEntry (i : Fin 77) : CNF (Atom 12) :=
  ⟨(moves i).flatMap (fun m => (minMove m).clauses)⟩

theorem model_minimumEntry (i : Fin 77) (f : Fin 12 → Fin 12 → Fin 12)
    (hf : Minimal i f) : (minimumEntry i).Sat (meaning f) := by
  simp only [minimumEntry,CNF.Sat,CNF.eval,Array.all_flatMap]
  rw [Array.all_eq_true_iff_forall_mem]
  intro m hm
  change (minMove m).Sat (meaning f)
  have hv := moves_valid i m hm
  let s : Equiv.Perm (Fin 12) := ⟨forward m, backward m, hv.1, hv.2.1⟩
  have hs := hf s hv.2.2.1 hv.2.2.2
  apply sat_all1; intro z
  apply sat_all1; intro w
  split
  · rename_i hwz
    apply sat_single
    by_cases hz : f 1 2 = z
    · have hw : f (backward m 1) (backward m 2) ≠ w := by
        intro hh
        change f 1 2 ≤ forward m (f (backward m 1) (backward m 2)) at hs
        rw [hz,hh] at hs
        exact (not_le_of_gt hwz) hs
      simp [CNF.Clause.eval,meaning,p,hw]
    · simp [CNF.Clause.eval,meaning,p,hz]
  · exact CNF.sat_empty

def idempotentTargets : CNF (Atom 12) :=
  all1 fun a => all1 fun b =>
    if a < b then all1 fun c =>
      ⟨#[[(p a a c,false),(p b b c,false),(p c c c,true)]]⟩
    else .empty

theorem model_idempotentTargets (hthree : threeFormula.Unsat) (hfour : fourFormula.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) : idempotentTargets.Sat (meaning f) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  split
  · rename_i hab
    apply sat_all1; intro c
    apply sat_single
    by_cases ha : f a a = c
    · by_cases hb : f b b = c
      · have hc := collision_target_idempotent hthree hfour f h a b c (ne_of_lt hab) ha hb
        simp [CNF.Clause.eval,meaning,p,hc]
      · simp [CNF.Clause.eval,meaning,p,hb]
    · simp [CNF.Clause.eval,meaning,p,ha]
  · exact CNF.sat_empty

def formula (i : Fin 77) : CNF (Atom 12) :=
  base ++ units (rowUnits (table i)) ++ minimumEntry i ++ idempotentTargets

def natFormula (i : Fin 77) : CNF ℕ := sanitize ((formula i).relabel code)

theorem no_fixed_row (i : Fin 77) (hn : (natFormula i).Unsat)
    (hthree : threeFormula.Unsat) (hfour : fourFormula.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hr : ∀ y, f 0 y = table i y) : False := by
  obtain ⟨g,hg,hgr,hgm⟩ := exists_minimal i f h hr
  have hu : UnitsHold (rowUnits (table i)) g := by
    intro u hum
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hum
    exact hgr y
  have sat : (formula i).Sat (meaning g) := by
    simp only [formula,CNF.Sat,CNF.eval_append,Bool.and_eq_true]
    exact ⟨⟨⟨model_base g hg, model_units _ g hu⟩, model_minimumEntry i g hgm⟩,
      model_idempotentTargets hthree hfour g hg⟩
  have raw : ((formula i).relabel code).Unsat := by
    intro a
    cases he : ((formula i).relabel code).eval a with
    | false => rfl
    | true =>
      have hs : (natFormula i).Sat a := by
        simp only [CNF.Sat,CNF.eval,natFormula,sanitize,Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      exact Bool.noConfusion hh
  have hh := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp raw (meaning g)
  rw [sat] at hh
  exact Bool.noConfusion hh

spectrum_assert no_fixed_row complete
end Spectrum.E667.Twelve.RowReduction
