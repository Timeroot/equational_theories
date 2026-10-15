import equational_theories.Spectrum.SmallOrders.Encoding
import equational_theories.Spectrum.SmallOrders.FewFixed
import equational_theories.ManuallyProved.Equation677

/-! Strengthen the small-order encoding by counting fixed points before
choosing zero. All models with unique left fixers have this normalization. -/
namespace Spectrum.SmallOrders.FewFixedEncoding
open Std.Sat
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sanitize)
open Encoding (Atom p meaning code code_injective)
variable {n : ℕ} [NeZero n]

def few : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val < z.val then
    ⟨#[[(p 0 0 0,true),(p 0 y y,false),(p 0 z z,false)]]⟩ else .empty

def formula (k : Kind) (n : ℕ) [NeZero n] : CNF (Atom n) :=
  Encoding.formula k n ++ few

def natFormula (k : Kind) (n : ℕ) [NeZero n] : CNF ℕ :=
  sanitize ((formula k n).relabel code)

lemma model_few (k : Kind) (f : Fin n → Fin n → Fin n)
    (hf : f 0 0 ≠ 0 → ∀ y z, f 0 y = y → f 0 z = z → y = z) :
    few.Sat (meaning k f) := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hyz
    apply sat_single
    by_cases h0 : f 0 0 = 0
    · simp [CNF.Clause.eval,meaning,p,h0]
    · have hh : ¬ (f 0 y = y ∧ f 0 z = z) := by
        rintro ⟨hy,hz⟩
        have := congrArg Fin.val (hf h0 y z hy hz)
        omega
      by_cases hy : f 0 y = y <;> simp_all [CNF.Clause.eval,meaning,p]
  · exact CNF.sat_empty

lemma model_formula (k : Kind) (f : Fin n → Fin n → Fin n) (h : Holds k f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hf : f 0 0 ≠ 0 → ∀ y z, f 0 y = y → f 0 z = z → y = z) :
    (formula k n).Sat (meaning k f) :=
  E63.OrderTen.Encoding.sat_append _ _ _ (Encoding.model_formula k f h hd hc)
    (model_few k f hf)

lemma no_model_of_unsat (k : Kind) (hn : (natFormula k n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds k f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hf : f 0 0 ≠ 0 → ∀ y z, f 0 y = y → f 0 z = z → y = z) : False := by
  have unsat_raw : ((formula k n).relabel code).Unsat := by
    intro a
    cases he : (((formula k n).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula k n).Sat a := by
        simp only [CNF.Sat, CNF.eval, natFormula, sanitize, Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp unsat_raw
  have hh := hn' (meaning k f)
  rw [model_formula k f h hd hc hf] at hh
  contradiction


omit [NeZero n] in
theorem fixers (k : Kind) (hk : k = .e677 ∨ rightLatin k = true)
    (f : Fin n → Fin n → Fin n) (h : Holds k f) :
    ∀ a b x, f a x = x → f b x = x → a = b := by
  intro a b x ha hb
  rcases hk with rfl | hk
  · letI : Magma (Fin n) := ⟨f⟩
    have he : Equation677 (Fin n) := fun x y => (h x y).symm
    exact (Eq677.eq677_fixer_unique he ha).trans (Eq677.eq677_fixer_unique he hb).symm
  · exact (right_bijective h hk x).1 (ha.trans hb.symm)

theorem not_hasModel (k : Kind) (hk : k = .e677 ∨ rightLatin k = true)
    (hn : (natFormula k n).Unsat) : ¬ k.law.HasModel n := by
  rintro ⟨M,hM⟩
  have h := (holds_iff k M).mpr hM
  obtain ⟨e,hd,hc,hf⟩ := FewFixed.normalized M.op (fixers k hk M.op h)
  exact no_model_of_unsat k hn (FewFixed.relabel M.op e) (holds_relabel h e) hd hc hf
end Spectrum.SmallOrders.FewFixedEncoding
