import equational_theories.Spectrum.Equation667FixedSquare.Encoding
import equational_theories.Spectrum.FiniteSearch.FirstUse

/-! Common finite-table clauses and first-use constraints for the collision
branches of the order-twelve proof. All solver input has a Lean soundness
proof; the refutations are supplied separately. -/
namespace Spectrum.E667.Twelve
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
open SmallPairs.Encoding (Atom p code code_injective)
open RightIdentityTwelve (Holds meaning)
open Spectrum.FiniteSearch

def base : CNF (Atom 12) :=
  RightIdentityTwelve.latin ++ RightIdentityTwelve.identities ++
  RightIdentityTwelve.middleLatin ++ RightIdentityTwelve.nonconstant ++
  FixedSquare.nonidempotent ++ FixedSquare.noRightIdentity ++
  RightIdentityTwelve.threeCycles ++ RightIdentityTwelve.twoCycles ++ RightIdentityTwelve.fibers

theorem model_base (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) : base.Sat (meaning f) := by
  simp only [base, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨RightIdentityTwelve.model_latin f h,
    RightIdentityTwelve.model_identities f h⟩, RightIdentityTwelve.model_middleLatin f h⟩,
    RightIdentityTwelve.model_nonconstant f h (by decide)⟩,
    FixedSquare.model_nonidempotent f h⟩, FixedSquare.model_noRightIdentity f h⟩,
    RightIdentityTwelve.model_threeCycles f h⟩, RightIdentityTwelve.model_twoCycles f h⟩,
    RightIdentityTwelve.model_fibers f h⟩

abbrev Entry := Fin 12 × Fin 12 × Fin 12
def units (us : List Entry) : CNF (Atom 12) :=
  ⟨us.toArray.map (fun u => [(p u.1 u.2.1 u.2.2,true)])⟩
def UnitsHold (us : List Entry) (f : Fin 12 → Fin 12 → Fin 12) : Prop :=
  ∀ u ∈ us, f u.1 u.2.1 = u.2.2

theorem model_units (us : List Entry) (f : Fin 12 → Fin 12 → Fin 12)
    (h : UnitsHold us f) : (units us).Sat (meaning f) := by
  simp only [units, CNF.Sat, CNF.eval, Array.all_map, List.all_toArray, List.all_eq_true]
  intro u hu
  simp [CNF.Clause.eval,meaning,p,h u hu]

def previous (z : Fin 12) : Fin 12 := ⟨z.val - 1, by omega⟩

def firstUse {m : ℕ} (k : ℕ) (cells : Fin m → Fin 12 × Fin 12) : CNF (Atom 12) :=
  all1 fun i => all1 fun z =>
    if k ≤ (previous z).val ∧ previous z < z ∧
        ∀ j ≤ i, (cells j).1 < previous z ∧ (cells j).2 < previous z then
      ⟨#[[(p (cells i).1 (cells i).2 z,false)] ++
        ((List.finRange m).filter (· < i)).map
          (fun j => (p (cells j).1 (cells j).2 (previous z),true))]⟩
    else .empty

def FirstUse {m : ℕ} (k : ℕ) (cells : Fin m → Fin 12 × Fin 12)
    (f : Fin 12 → Fin 12 → Fin 12) : Prop :=
  ∀ (i : Fin m) (a b : Fin 12), k ≤ a.val → a < b →
    (∀ j ≤ i, (cells j).1 < a ∧ (cells j).2 < a) →
    f (cells i).1 (cells i).2 = b → ∃ j < i, f (cells j).1 (cells j).2 = a

theorem model_firstUse {m : ℕ} (k : ℕ) (cells : Fin m → Fin 12 × Fin 12)
    (f : Fin 12 → Fin 12 → Fin 12) (h : FirstUse k cells f) :
    (firstUse k cells).Sat (meaning f) := by
  apply sat_all1; intro i
  apply sat_all1; intro z
  split
  · rename_i hz
    apply sat_single
    by_cases he : f (cells i).1 (cells i).2 = z
    · obtain ⟨j,hj,hf⟩ := h i (previous z) z hz.1 hz.2.1 hz.2.2 he
      simp only [CNF.Clause.eval, List.any_append, Bool.or_eq_true]
      right
      simp only [List.any_map, List.any_eq_true]
      exact ⟨j, List.mem_filter.mpr ⟨List.mem_finRange _,by simpa using hj⟩,
        by simpa [meaning,p] using hf⟩
    · simp [CNF.Clause.eval, meaning,p,he]
  · exact CNF.sat_empty

theorem exists_normalized {m : ℕ} (k : ℕ) (cells : Fin m → Fin 12 × Fin 12)
    (us : List Entry) (hu : ∀ u ∈ us, u.1.val < k ∧ u.2.1.val < k ∧ u.2.2.val < k)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hus : UnitsHold us f) :
    ∃ g : Fin 12 → Fin 12 → Fin 12, Holds g ∧ UnitsHold us g ∧ FirstUse k cells g := by
  obtain ⟨e,he,hn⟩ := exists_first_use f cells k
  refine ⟨relabel f e, RightIdentityTwelve.holds_relabel h e, ?_, hn⟩
  have hsym (x : Fin 12) (hx : x.val < k) : e.symm x = x := by
    apply e.injective
    rw [Equiv.apply_symm_apply,he x hx]
  intro u hum
  have hb := hu u hum
  simp only [relabel,hsym u.1 hb.1,hsym u.2.1 hb.2.1,hus u hum,he u.2.2 hb.2.2]

def natFormula {m : ℕ} (k : ℕ) (cells : Fin m → Fin 12 × Fin 12) (us : List Entry) : CNF ℕ :=
  sanitize ((base ++ units us ++ firstUse k cells).relabel code)

theorem no_model {m : ℕ} (k : ℕ) (cells : Fin m → Fin 12 × Fin 12)
    (us : List Entry) (hu : ∀ u ∈ us, u.1.val < k ∧ u.2.1.val < k ∧ u.2.2.val < k)
    (hn : (natFormula k cells us).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hus : UnitsHold us f) : False := by
  obtain ⟨g,hg,hgu,hgn⟩ := exists_normalized k cells us hu f h hus
  have sat : (base ++ units us ++ firstUse k cells).Sat (meaning g) :=
    sat_append _ _ _ (sat_append _ _ _ (model_base g hg) (model_units us g hgu))
      (model_firstUse k cells g hgn)
  have raw : ((base ++ units us ++ firstUse k cells).relabel code).Unsat := by
    intro a
    cases he : ((base ++ units us ++ firstUse k cells).relabel code).eval a with
    | false => rfl
    | true =>
      have hs : (natFormula k cells us).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hh := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp raw (meaning g)
  rw [sat] at hh
  contradiction

spectrum_assert no_model complete
end Spectrum.E667.Twelve
