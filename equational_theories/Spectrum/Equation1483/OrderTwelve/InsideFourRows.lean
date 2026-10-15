import equational_theories.Spectrum.Equation1483.OrderTwelve.InsideFourRowOrbits
import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadLexEncoding

/-! The all-zero rank-four head has only twenty-one sorted first rows, in five
isomorphism orbits. Coverage and the five representative exclusions are checked
separately; none of the row enumeration is assumed to be exhaustive. -/
namespace Spectrum.E1483.OrderTwelve.InsideFourRows
open Std.Sat Magma.Central1483.CNF
open RowsData

def rowCells (r : Row) : List Encoding.Cell :=
  (List.finRange 12).map fun y => (0,y,r y)

def rowFormula (r : Row) : CNF Nat := HeadLexEncoding.toNat 4 true (rowCells r)
def headCells : List Encoding.Cell := [(0,0,0),(0,2,0),(0,3,0)]
def base : CNF Nat := HeadLexEncoding.toNat 4 true headCells

def excludedRow (r : Row) : CNF.Clause Nat :=
  (List.finRange 12).map fun y => (code (p 0 y (r y)),false)

def coverage : CNF Nat := base ++
  ⟨((List.finRange 21).map fun i => excludedRow (row i)).toArray⟩

lemma model_nat (f : A → A → A) (h : NormalForm f 4 true)
    (h0 : f 0 0 = 0) (h2 : f 0 2 = 0) (h3 : f 0 3 = 0) :
    ∃ a : Nat → Bool, base.Sat a ∧
      ∀ x y z, a (code (p x y z)) = decide (f x y = z) := by
  classical
  let a : Nat → Bool := Function.extend HeadLexEncoding.number
    (HeadLexEncoding.assignment f) (fun _ => false)
  have ha : a ∘ HeadLexEncoding.number = HeadLexEncoding.assignment f :=
    Function.extend_comp HeadLexEncoding.number_injective _ _
  have hf := HeadLexEncoding.model_formula 4 true headCells f h.bounds.2 h.core h.sorted
    (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
    (by intro c hc; simp only [headCells,List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl|rfl|rfl <;> assumption)
  have hs : ((HeadLexEncoding.formula 4 true headCells).relabel HeadLexEncoding.number).Sat a := by
    apply CNF.sat_relabel
    rw [ha]
    exact hf
  refine ⟨a,sat_sanitize _ a hs,?_⟩
  intro x y z
  have he := congrFun ha (HeadLexEncoding.old (p x y z))
  simpa [Function.comp_def,HeadLexEncoding.number,HeadLexEncoding.old,
    HeadLexEncoding.assignment,meaning,p] using he

lemma no_row (r : Row) (hn : (rowFormula r).Unsat)
    (f : A → A → A) (h : NormalForm f 4 true) (hr : ∀ y, f 0 y = r y) : False := by
  apply HeadLexEncoding.no_model 4 true (rowCells r) hn f h.bounds.2 h.core h.sorted
    (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex
  intro c hc
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hc
  exact hr y

lemma no_zero_head
    (hcases : ∀ j : Fin 5, (rowFormula (row (representative j))).Unsat)
    (hcoverage : coverage.Unsat)
    (f : A → A → A) (h : NormalForm f 4 true)
    (h0 : f 0 0 = 0) (h2 : f 0 2 = 0) (h3 : f 0 3 = 0) : False := by
  classical
  obtain ⟨a,ha,hval⟩ := model_nat f h h0 h2 h3
  have hall (i : Fin 21) : CNF.Clause.eval a (excludedRow (row i)) = true := by
    by_cases he : ∃ y, f 0 y ≠ row i y
    · obtain ⟨y,hy⟩ := he
      simp only [excludedRow,CNF.Clause.eval,List.any_map,List.any_eq_true]
      exact ⟨y,List.mem_finRange _,by simp [hval,hy]⟩
    · have hr : ∀ y, f 0 y = row i y := by simpa only [not_exists,not_not] using he
      obtain ⟨g,hg,hgr⟩ := InsideFourRowOrbits.exists_normalForm f h.core h.sorted i hr
      exact (no_row _ (hcases (target i)) g hg hgr).elim
  have hs : coverage.Sat a := by
    apply sat_append
    · exact ha
    simp only [CNF.Sat,CNF.eval,List.all_toArray,List.all_map,List.all_eq_true]
    intro i _
    exact hall i
  exact Bool.false_ne_true ((hcoverage a).symm.trans hs)
end Spectrum.E1483.OrderTwelve.InsideFourRows
