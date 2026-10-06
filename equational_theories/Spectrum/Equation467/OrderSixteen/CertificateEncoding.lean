import equational_theories.Spectrum.Equation467.OrderSixteen.Encoding
import equational_theories.Spectrum.Equation467.OrderSixteen.Refs

namespace Spectrum.E467.OrderSixteen.Encoding
open Std.Sat
open E63.OrderTen.Encoding (Atom p meaning sat_single sat_append code)

def returnUnits (r : Ref) : CNF (Atom 16) := match refValue r with
  | none => .empty
  | some v => ⟨#[[(p 0 (inverseDiagonal (refCase r) 0) v,true)]]⟩

def refFormula (r : Ref) : CNF (Atom 16) := formula (refCase r) ++ returnUnits r

def natRefWith (base : CNF ℕ) (r : Ref) : CNF ℕ :=
  base ++ sanitize ((returnUnits r).relabel code)

def natRef (r : Ref) : CNF ℕ := natRefWith (natFormula (refCase r)) r

private theorem sanitize_append (F G : CNF ℕ) : sanitize (F ++ G) = sanitize F ++ sanitize G := by
  change (⟨(F.clauses ++ G.clauses).filter _⟩ : CNF ℕ) =
    ⟨F.clauses.filter _ ++ G.clauses.filter _⟩
  rw [Array.filter_append]
  simp

theorem natRef_eq (r : Ref) : natRef r = sanitize ((refFormula r).relabel code) := by
  simp only [natRef,natRefWith,natFormula,refFormula,CNF.relabel_append,sanitize_append]

theorem model_ref (i : Case) (f : Point → Point → Point) (hf : InCase i f)
    (hm : Minimal i f) :
    (refFormula (selectRef i (f 0 (inverseDiagonal i 0)))).Sat (meaning f) := by
  obtain ⟨hc,hv⟩ := select_checked i (f 0 (inverseDiagonal i 0))
  apply sat_append
  · rw [hc]
    exact model_formula i f hf hm
  · rcases hv with hv | hv
    · simp only [returnUnits,hv]
      exact CNF.sat_empty
    · simp only [returnUnits,hv,hc]
      apply sat_single
      simp [CNF.Clause.eval,meaning,p]

/-- The chosen certificate case includes the actual return value of the
hypothetical normalized model, so its clauses must be satisfiable. -/
theorem impossible_of_certificates (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) (hu : ∀ r : Ref, (natRef r).Unsat) : False := by
  let r := selectRef i (f 0 (inverseDiagonal i 0))
  have hu' : ((refFormula r).relabel code).Unsat := by
    intro a
    cases he : (((refFormula r).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natRef r).Sat a := by
        rw [natRef_eq]
        simp only [CNF.Sat,CNF.eval,sanitize,Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hu r a
      rw [hs] at hh
      exact Bool.noConfusion hh
  have hraw := (CNF.unsat_relabel_iff (fun _ _ he => code16_injective he)).mp hu'
  have hh := hraw (meaning f)
  rw [model_ref i f hf hm] at hh
  contradiction

end Spectrum.E467.OrderSixteen.Encoding
