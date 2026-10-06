import equational_theories.Spectrum.Equation667FixedSquare.Encoding
import equational_theories.Spectrum.FiniteSearch.FirstUse

/-! Symmetry breaking that preserves the prescribed square map. All moves
used in a clause commute with that map; arbitrary row normalization would
not have this property. -/
namespace Spectrum.E667.FixedSquare
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open SmallPairs.Encoding (Atom p code code_injective)
open RightIdentityTwelve (Holds meaning)
open Spectrum.FiniteSearch

def moves (d : Fin 12 → Fin 12) : List (Equiv.Perm (Fin 12)) :=
  let fixed := (List.finRange 12).filter (fun x => d x = x)
  let pairs := (List.finRange 12).filter (fun x => x < d x)
  let candidates :=
    fixed.flatMap (fun a => (fixed.filter (a < ·)).map (Equiv.swap a)) ++
    pairs.map (fun a => Equiv.swap a (d a)) ++
    pairs.flatMap (fun a => (pairs.filter (a < ·)).map
      (fun b => (Equiv.swap a b).trans (Equiv.swap (d a) (d b))))
  candidates.filter (fun s => ∀ x, s (d x) = d (s x))

def firstUseMove (s : Equiv.Perm (Fin 12)) : CNF (Atom 12) :=
  all1 fun y =>
    if s 0 = 0 ∧ ∀ t ≤ y, s t = t then all1 fun z =>
      if s z < z then
        ⟨#[[(p 0 y z,false)] ++
          ((List.finRange 12).filter (· < y)).flatMap (fun t =>
            ((List.finRange 12).filter (fun w => s w ≠ w)).map
              (fun w => (p 0 t w,true))) ]⟩
      else .empty
    else .empty

def firstUse (d : Fin 12 → Fin 12) : CNF (Atom 12) :=
  ⟨(moves d).toArray.flatMap (fun s => (firstUseMove s).clauses)⟩

def FirstUse (d : Fin 12 → Fin 12) (f : Fin 12 → Fin 12 → Fin 12) : Prop :=
  ∀ s : Equiv.Perm (Fin 12), (∀ x, s (d x) = d (s x)) → ∀ y : Fin 12,
    (s 0 = 0 ∧ ∀ t ≤ y, s t = t) → (∀ t < y, s (f 0 t) = f 0 t) →
    f 0 y ≤ s (f 0 y)

theorem model_firstUseMove (d : Fin 12 → Fin 12) (f : Fin 12 → Fin 12 → Fin 12)
    (h : FirstUse d f) (s : Equiv.Perm (Fin 12))
    (hs : ∀ x, s (d x) = d (s x)) : (firstUseMove s).Sat (meaning f) := by
  apply sat_all1; intro y
  split
  · rename_i hy
    apply sat_all1; intro z
    split
    · rename_i hz
      apply sat_single
      by_cases he : f 0 y = z
      · have hex : ∃ t < y, s (f 0 t) ≠ f 0 t := by
          by_contra! hn
          have hh := h s hs y hy hn
          rw [he] at hh
          exact (not_le_of_gt hz) hh
        obtain ⟨t,ht,hst⟩ := hex
        simp only [CNF.Clause.eval, List.any_append, Bool.or_eq_true]
        right
        simp only [List.any_flatMap, List.any_eq_true, List.any_map]
        refine ⟨t, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using ht⟩, ?_⟩
        refine ⟨f 0 t, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using hst⟩, ?_⟩
        simp [meaning,p]
      · simp [CNF.Clause.eval, meaning,p,he]
    · exact CNF.sat_empty
  · exact CNF.sat_empty

theorem model_firstUse (d : Fin 12 → Fin 12) (f : Fin 12 → Fin 12 → Fin 12)
    (h : FirstUse d f) : (firstUse d).Sat (meaning f) := by
  simp only [firstUse, CNF.Sat, CNF.eval, Array.all_flatMap,
    List.all_toArray, List.all_eq_true]
  intro s hs
  apply model_firstUseMove d f h s
  exact of_decide_eq_true (List.mem_filter.mp hs).2

theorem exists_normalized (d : Fin 12 → Fin 12) (f : Fin 12 → Fin 12 → Fin 12)
    (h : Holds f) (hd : ∀ x, f x x = d x) :
    ∃ g : Fin 12 → Fin 12 → Fin 12, Holds g ∧ (∀ x, g x x = d x) ∧ FirstUse d g := by
  obtain ⟨e,hed,_,he⟩ := exists_centralizer_first_use f d ∅ (fun y : Fin 12 => (0,y))
  refine ⟨relabel f e, RightIdentityTwelve.holds_relabel h e, ?_, ?_⟩
  · intro x
    simp only [relabel, hd, hed, Equiv.apply_symm_apply]
  · intro s hs y hy hout
    exact he s hs (by simp) y (fun t ht => ⟨hy.1,hy.2 t ht⟩) hout

def normalizedFormula (d : Fin 12 → Fin 12) (normalize : Bool) : CNF (Atom 12) :=
  formula d ++ if normalize then firstUse d else .empty

def natNormalized (d : Fin 12 → Fin 12) (normalize : Bool) : CNF ℕ :=
  sanitize ((normalizedFormula d normalize).relabel code)

theorem no_model_normalized (d : Fin 12 → Fin 12) (normalize : Bool)
    (hn : (natNormalized d normalize).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hd : ∀ x, f x x = d x) : False := by
  obtain ⟨g,hg,hgd,hgn⟩ := exists_normalized d f h hd
  have sat : (normalizedFormula d normalize).Sat (meaning g) := by
    apply sat_append
    · exact model_formula g hg d hgd
    · cases normalize with
      | false => exact CNF.sat_empty
      | true => exact model_firstUse d g hgn
  have raw : ((normalizedFormula d normalize).relabel code).Unsat := by
    intro a
    cases he : ((normalizedFormula d normalize).relabel code).eval a with
    | false => rfl
    | true =>
      have hs : (natNormalized d normalize).Sat a := by
        simp only [CNF.Sat, CNF.eval, natNormalized, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hh := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp raw (meaning g)
  rw [sat] at hh
  contradiction

spectrum_assert no_model_normalized complete
end Spectrum.E667.FixedSquare
