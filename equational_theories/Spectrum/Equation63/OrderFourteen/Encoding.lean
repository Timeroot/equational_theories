import equational_theories.Spectrum.Equation63.OrderTen.Encoding
import equational_theories.Spectrum.Equation63.OrderFourteen.Normalization

/-! The old Latin/cubic encoding, with the fixed-point counting consequence.
Every atom still means one table entry; no cardinality-network variables or
unproved symmetry assumptions are needed. -/
namespace Spectrum.E63.OrderFourteen.Encoding
open Std.Sat OrderTen.Encoding OrderTen

private def atMostOne (n : ℕ) [NeZero n] : CNF (Atom n) :=
  all1 fun y => all1 fun z => if y.val < z.val then
    ⟨#[[(p 0 y y,false),(p 0 z z,false)]]⟩ else .empty

private def fixedRows (n : ℕ) [NeZero n] : CNF (Atom n) :=
  all1 fun y => all1 fun x =>
    ⟨#[ (p 0 y y,false) :: (List.finRange n).map (fun z => (p x z z,true))]⟩ ++
    all1 fun z => all1 fun w => if z.val < w.val then
      ⟨#[[(p 0 y y,false),(p x z z,false),(p x w w,false)]]⟩ else .empty

def formula : CNF (Atom 14) := OrderTen.Encoding.formula 14 ++ atMostOne 14 ++ fixedRows 14

def natFormula : CNF ℕ := sanitize (formula.relabel code)

lemma model_atMostOne {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin n)
    (hf : FixedRule f) : (atMostOne n).Sat (meaning f) := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hyz
    apply sat_single
    have hh : ¬ (f 0 y = y ∧ f 0 z = z) := by
      rintro ⟨hy,hz⟩
      rcases hf with hf | hf
      · exact hf y hy
      · obtain ⟨w,hw,hu⟩ := hf 0
        have he := congrArg Fin.val ((hu y hy).trans (hu z hz).symm)
        omega
    by_cases hy : f 0 y = y <;> simp_all [CNF.Clause.eval,meaning,p]
  · exact CNF.sat_empty

lemma model_fixedRows {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin n)
    (hf : FixedRule f) : (fixedRows n).Sat (meaning f) := by
  apply sat_all1; intro y
  apply sat_all1; intro x
  have hh (hy : f 0 y = y) : ∃! z, f x z = z := by
    rcases hf with hf | hf
    · exact (hf y hy).elim
    · exact hf x
  apply sat_append
  · apply sat_single
    by_cases hy : f 0 y = y
    · obtain ⟨z,hz,_⟩ := hh hy
      simp only [CNF.Clause.eval,List.any_cons,meaning,p,hy,decide_true,
        Bool.or_eq_true,List.any_map,List.any_eq_true]
      exact Or.inr ⟨z, List.mem_finRange _, by simpa [meaning,p] using hz⟩
    · simp [CNF.Clause.eval,meaning,p,hy]
  · apply sat_all1; intro z
    apply sat_all1; intro w
    split
    · rename_i hzw
      apply sat_single
      have hbad : ¬ (f 0 y = y ∧ f x z = z ∧ f x w = w) := by
        rintro ⟨hy,hz,hw⟩
        obtain ⟨a,ha,hu⟩ := hh hy
        have he := congrArg Fin.val ((hu z hz).trans (hu w hw).symm)
        omega
      by_cases hy : f 0 y = y <;> by_cases hz : f x z = z <;>
        simp_all [CNF.Clause.eval,meaning,p]
    · exact CNF.sat_empty

lemma model_formula (f : Fin 14 → Fin 14 → Fin 14) (h : Cubic f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) (hf : FixedRule f) :
    formula.Sat (meaning f) :=
  sat_append _ _ _ (sat_append _ _ _ (OrderTen.Encoding.model_formula f h hd hc)
    (model_atMostOne f hf)) (model_fixedRows f hf)

lemma code_injective : Function.Injective (@code 14) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ he
  dsimp [code] at he
  have hz : z = z' := Fin.ext (by omega)
  have hy : y = y' := Fin.ext (by omega)
  have hx : x = x' := Fin.ext (by omega)
  exact Prod.ext hx (Prod.ext hy hz)

lemma no_model_of_unsat (hn : natFormula.Unsat) (f : Fin 14 → Fin 14 → Fin 14)
    (h : Cubic f) (hd : f 0 0 = 0 → ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) (hf : FixedRule f) : False := by
  have unsat_raw : (formula.relabel code).Unsat := by
    intro a
    cases he : ((formula.relabel code).eval a) with
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
  rw [model_formula f h hd hc hf] at hh
  contradiction

end Spectrum.E63.OrderFourteen.Encoding
