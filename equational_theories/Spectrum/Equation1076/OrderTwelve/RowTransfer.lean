import equational_theories.Spectrum.Equation1076.OrderTwelve.CanonicalData
import equational_theories.Spectrum.Equation1076.ShortCycles

/-! Reuse one refutation for all orderings of the same translation cycles.
Only the finite relabeling data are computational; the transfer itself is a
usual isomorphism argument on operations. The completed order-12 exclusion
uses this coverage encoding together with the finer cases in PointEncoding. -/
namespace Spectrum.E1076.OrderTwelve.RowTransfer
open Std.Sat SmallOrders SmallOrders.Encoding CanonicalData SmallOrders.CaseAssembly
open E63.OrderTen.Encoding (sat_append sanitize)

abbrev Matches (f : Fin 12 → Fin 12 → Fin 12) (r : Row) : Prop := ∀ y, f 0 y = r y

def units (r : Row) : List ℕ := (List.finRange 12).map fun y => code (p 0 y (r y))
def rowFormula (r : Row) : CNF ℕ := caseFormula (ShortCycles.natFormula 12) (units r)
def allRows : List (List ℕ) := (List.finRange 13).map fun i => units (row i)
def coverage : CNF ℕ := coverFormula (ShortCycles.natFormula 12) allRows

/-- A model induces a Boolean assignment satisfying the actual numbered CNF. -/
theorem model_nat (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) :
    ∃ a : ℕ → Bool, (ShortCycles.natFormula 12).Sat a ∧
      ∀ x y z, a (code (p x y z)) = decide (f x y = z) := by
  classical
  let a : ℕ → Bool := Function.extend code (meaning .e1076 f) (fun _ => false)
  have ha : a ∘ code = meaning .e1076 f := Function.extend_comp Encoding.code_injective _ _
  have hs : ((ShortCycles.formula 12).relabel code).Sat a := by
    apply CNF.sat_relabel
    rw [ha]
    exact ShortCycles.model_formula f h hd hc
  refine ⟨a, ?_, fun x y z => congrFun ha (p x y z)⟩
  simp only [CNF.Sat,CNF.eval,ShortCycles.natFormula,sanitize,
    Array.all_eq_true_iff_forall_mem] at hs ⊢
  exact fun c hc => hs c (Array.mem_filter.mp hc).1

theorem no_row (r : Row) (hr : (rowFormula r).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hm : Matches f r) : False := by
  obtain ⟨a,ha,hval⟩ := model_nat f h hd hc
  have hu : ∀ v ∈ units r, a v = true := by
    intro v hv
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hv
    simpa [hm y] using hval 0 y (r y)
  have hs := case_sat (ShortCycles.natFormula 12) (units r) a ha hu
  have hh := hr a
  change (caseFormula (ShortCycles.natFormula 12) (units r)).eval a = false at hh
  rw [hs] at hh
  contradiction

/-- A checked representative row excludes every cycle ordering conjugate to it. -/
theorem no_row_from_representative (i : Fin 13)
    (hr : (rowFormula (row (representative (target i)))).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hm : Matches f (row i)) : False := by
  let e := permutation i
  have he : e 0 = 0 := zero_fixed i
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let g (x y : Fin 12) := e (f (e.symm x) (e.symm y))
  have hg : Matches g (row (representative (target i))) := by
    intro y
    simpa only [g,he',hm] using conjugates i y
  apply no_row _ hr g (holds_relabel h e) ?_ ?_ hg
  · intro h0 x
    have hh : f 0 0 = 0 := by
      apply e.injective
      simpa only [g,he',he] using h0
    simp only [g,hd hh,Equiv.apply_symm_apply]
  · intro y
    rw [hg y]
    exact chain_checked (target i) y

/-- Coverage is itself a checked CNF refutation, avoiding a trusted enumeration
or a separate theorem classifying all twelve-point permutations. -/
theorem no_model (hcases : ∀ j : Fin 6, (rowFormula (row (representative j))).Unsat)
    (hcoverage : coverage.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : False := by
  obtain ⟨a,ha,hval⟩ := model_nat f h hd hc
  have hall (i : Fin 13) : CNF.Clause.eval a ((units (row i)).map fun v => (v,false)) = true := by
    by_cases he : ∃ y, f 0 y ≠ row i y
    · obtain ⟨y,hy⟩ := he
      simp only [CNF.Clause.eval,List.any_map,List.any_eq_true]
      refine ⟨code (p 0 y (row i y)), List.mem_map.mpr ⟨y,List.mem_finRange _,rfl⟩, ?_⟩
      simp [hval 0 y (row i y),hy]
    · have hm : Matches f (row i) := by simpa only [not_exists,not_not] using he
      exact (no_row_from_representative i (hcases (target i)) f h hd hm).elim
  have hs : coverage.Sat a := by
    apply sat_append
    · exact ha
    simp only [CNF.Sat,CNF.eval,allRows,List.all_toArray,List.all_map,List.all_eq_true]
    intro i _
    exact hall i
  have hh := hcoverage a
  rw [hs] at hh
  contradiction

end Spectrum.E1076.OrderTwelve.RowTransfer
