import equational_theories.Spectrum.Equation63.OrderTen.Encoding

/-! Gluing finite refutations while keeping each branch's assumptions as root
units. This avoids repropagating the same assumptions at every proof step. The
short coverage refutation checks that the branch list is exhaustive. -/
namespace Spectrum.SmallOrders.CaseAssembly
open Std.Sat

def caseFormula (F : CNF ℕ) (units : List ℕ) : CNF ℕ :=
  F ++ ⟨(units.map fun v => [(v,true)]).toArray⟩

def coverFormula (F : CNF ℕ) (patterns : List (List ℕ)) : CNF ℕ :=
  F ++ ⟨(patterns.map fun us => us.map fun v => (v,false)).toArray⟩

lemma case_sat (F : CNF ℕ) (units : List ℕ) (a : ℕ → Bool)
    (hF : F.Sat a) (hu : ∀ v ∈ units, a v = true) : (caseFormula F units).Sat a := by
  apply Spectrum.E63.OrderTen.Encoding.sat_append
  · exact hF
  simp only [CNF.Sat,CNF.eval,List.all_toArray,List.all_map,List.all_eq_true]
  intro v hv
  simp [CNF.Clause.eval,hu v hv]

/-- Case lists and external proof transformations carry no trust: each case
and the completeness of their union are independently refuted. -/
theorem unsat_of_cases (F : CNF ℕ) (patterns : List (List ℕ))
    (hc : ∀ us ∈ patterns, (caseFormula F us).Unsat)
    (hcover : (coverFormula F patterns).Unsat) : F.Unsat := by
  intro a
  cases hF : F.eval a with
  | false => rfl
  | true =>
    have hall (us : List ℕ) (hus : us ∈ patterns) :
        CNF.Clause.eval a (us.map fun v => (v,false)) = true := by
      by_cases he : ∃ v ∈ us, a v = false
      · obtain ⟨v,hv,ha⟩ := he
        simp only [CNF.Clause.eval,List.any_map,List.any_eq_true]
        exact ⟨v,hv,by simpa using ha⟩
      · have hu : ∀ v ∈ us, a v = true := by
          intro v hv
          cases ha : a v
          · exact (he ⟨v,hv,ha⟩).elim
          · rfl
        have hh := hc us hus a
        rw [case_sat F us a hF hu] at hh
        contradiction
    have hs : (coverFormula F patterns).Sat a := by
      apply Spectrum.E63.OrderTen.Encoding.sat_append
      · exact hF
      simp only [CNF.Sat,CNF.eval,List.all_toArray,List.all_map,List.all_eq_true]
      exact hall
    have hh := hcover a
    rw [hs] at hh
    contradiction

end Spectrum.SmallOrders.CaseAssembly
