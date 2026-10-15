import equational_theories.Spectrum.Equation1483.OrderTwelve.RowOneNormalization
import equational_theories.Spectrum.Equation1483.OrderTwelve.ImageEncoding

/-! CNF for first mentions in the second row, under the remaining first-row
fiber permutations. These are proved symmetry restrictions, not new laws. -/
namespace Spectrum.E1483.OrderTwelve.RowOneEncoding
open Std.Sat Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization RowOneNormalization
abbrev A := Fin 12

def prior (a b i : A) : CNF.Clause (Atom 12) := (List.finRange 12).flatMap fun j =>
  if j < i then [(p 1 j a,true),(p 1 j b,true)] else []

def extras (k : Nat) (zero : Bool) : CNF (Atom 12) :=
  all1 fun a => all1 fun b => all1 fun i => all1 fun u =>
  if bound k zero < a.val ∧ a < b ∧ i < a ∧ u.val ≤ k then
    ⟨#[[(p 0 a u,false),(p 0 b u,false),(col 0 a,true),(col 0 b,true),(p 1 i b,false)] ++ prior a b i]⟩
  else .empty

def formula (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF (Atom 12) :=
  ImageEncoding.fixedFormula k zero cells ++ extras k zero

def toNat (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((formula k zero cells).relabel code)

lemma model_prior (f : A → A → A) (a b i : A)
    (h : ∃ j : A, j < i ∧ (f 1 j = a ∨ f 1 j = b)) :
    CNF.Clause.eval (meaning f) (prior a b i) = true := by
  obtain ⟨j,hj,he⟩ := h
  simp only [CNF.Clause.eval,prior,List.any_flatMap,List.any_eq_true]
  refine ⟨j,List.mem_finRange _,?_⟩
  rcases he with he|he <;> simp [hj,meaning,p,he]

lemma model_extras (f : A → A → A) (k : Nat) (zero : Bool)
    (hm : FirstMention f k zero) : CNF.Sat (meaning f) (extras k zero) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_all1; intro i
  apply sat_all1; intro u
  split
  next hc =>
    apply sat_single
    by_cases ha : f 0 a = u
    swap
    · simp [CNF.Clause.eval,meaning,p,ha]
    by_cases hb : f 0 b = u
    swap
    · simp [CNF.Clause.eval,meaning,p,hb]
    by_cases hca : ∃ x, f x 0 = a
    · simp [CNF.Clause.eval,meaning,col,hca]
    by_cases hcb : ∃ x, f x 0 = b
    · simp [CNF.Clause.eval,meaning,col,hcb]
    by_cases hi : f 1 i = b
    swap
    · simp [CNF.Clause.eval,meaning,p,hi]
    have hp := model_prior f a b i (hm a b i hc.1 hc.2.1 hc.2.2.1 hca hcb
      (ha.trans hb.symm) hi)
    simp only [CNF.Clause.eval,List.any_append]
    simp only [CNF.Clause.eval] at hp
    rw [hp,Bool.or_true]
  next => exact CNF.sat_empty

lemma no_model (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (toNat k zero cells).Unsat)
    (f : A → A → A) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) (hm : FirstMention f k zero)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (formula k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp (unsat_of_sanitize _ hn)
  have hf := sat_append _ _ _
    (sat_append _ _ _
      (sat_append _ _ _ (ImageEncoding.model_formula f k zero h hs) (ImageEncoding.model_firstTwo f ht))
      (Encoding.model_units f cells hc))
    (model_extras f k zero hm)
  exact Bool.false_ne_true ((hn' (meaning f)).symm.trans hf)

end Spectrum.E1483.OrderTwelve.RowOneEncoding
