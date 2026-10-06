import equational_theories.Spectrum.Equation667IdempotentFifteen.Canonical
import equational_theories.Spectrum.Equation667IdempotentTwelve.Encoding

namespace Spectrum.E667.IdempotentFifteen
open Std.Sat
open E63.OrderTen E63.OrderTen.Encoding

def rowUnits (i : Fin 13) : CNF (Atom 15) :=
  all1 fun y => ⟨#[[(p 0 y (row i y),true)]]⟩
def formula (i : Fin 13) : CNF (Atom 15) := IdempotentTwelve.formula 15 ++ rowUnits i
def natFormula (i : Fin 13) : CNF ℕ := sanitize ((formula i).relabel code)

private theorem code_inj : Function.Injective (@code 15) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ he
  dsimp [code] at he
  have hz : z = z' := Fin.ext (by omega)
  have hy : y = y' := Fin.ext (by omega)
  have hx : x = x' := Fin.ext (by omega)
  exact Prod.ext hx (Prod.ext hy hz)

private theorem model_case (i : Fin 13) (f : Fin 15 → Fin 15 → Fin 15)
    (h : Cubic f) (hi : ∀ x, f x x = x) (hr : f 0 = row i) :
    (formula i).Sat (meaning f) := by
  have hb : ∀ y, (f 0 y).val ≤ y.val + 1 := by rw [hr]; exact row_chain i
  apply sat_append
  · apply sat_append
    · exact model_formula f h (fun _ => hi) hb
    · apply sat_all1; intro x
      apply sat_single
      simp [CNF.Clause.eval, meaning, p, hi]
  · apply sat_all1; intro y
    apply sat_single
    simp [CNF.Clause.eval, meaning, p, congrFun hr y]

private theorem no_case (i : Fin 13) (hn : (natFormula i).Unsat)
    (f : Fin 15 → Fin 15 → Fin 15) (h : Cubic f) (hi : ∀ x, f x x = x)
    (hr : f 0 = row i) : False := by
  have raw : ((formula i).relabel code).Unsat := by
    intro a
    cases he : ((formula i).relabel code).eval a with
    | false => rfl
    | true =>
      have ht : (natFormula i).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [ht] at hh
      contradiction
  have hh := (CNF.unsat_relabel_iff (fun _ _ he => code_inj he)).mp raw (meaning f)
  rw [model_case i f h hi hr] at hh
  contradiction

/-- The row-coverage computation only ranges over chain rows, whose
exhaustive coverage is proved for arbitrary finite sizes. -/
theorem no_cubic_model (hn : ∀ i, (natFormula i).Unsat)
    (f : Fin 15 → Fin 15 → Fin 15) (h : Cubic f) (hi : ∀ x, f x x = x) : False := by
  obtain ⟨e,he,hb⟩ := exists_chain_label (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let g (x y : Fin 15) := e (f (e.symm x) (e.symm y))
  have hg : Cubic g := cubic_relabel h e
  have gi (x : Fin 15) : g x x = x := by simp only [g,hi,Equiv.apply_symm_apply]
  have gc (y : Fin 15) : (g 0 y).val ≤ y.val + 1 := by
    simpa only [g,he'] using hb y
  have ga : admissible (g 0) = true := by
    apply decide_eq_true
    refine ⟨gi 0, fun x hx => ?_⟩
    have fixed : g 0 x = x := (no_two_cycle hg 0 x (g 0 x) rfl hx).symm
    exact (right_injective hg x (fixed.trans (gi x).symm)).symm
  obtain ⟨hz,r,hr,hmap⟩ := covers (g 0) (left_injective hg 0) gc ga
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  let s := relabel (g 0)
  have hs : s.symm 0 = 0 := by apply s.injective; simpa only [Equiv.apply_symm_apply] using hz.symm
  let q (x y : Fin 15) := s (g (s.symm x) (s.symm y))
  apply no_case i (hn i) q (cubic_relabel hg s)
  · intro x
    simp only [q,gi,Equiv.apply_symm_apply]
  · funext y
    simpa only [q,hs,s,Equiv.apply_symm_apply] using hmap (s.symm y)

end Spectrum.E667.IdempotentFifteen
