import equational_theories.Spectrum.SmallOrders.Encoding
import equational_theories.Spectrum.Equation1110.SquareNormalization

/-! E1110 encodings that normalize the squaring permutation instead of a row.
The algebraic part is shared with the checked small-order chain encoding. -/
namespace Spectrum.E1110.SquareEncoding
open Std.Sat SmallOrders
open SmallOrders.Encoding (Atom p meaning code code_injective)
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)

variable {n : ℕ} [NeZero n]

def base (n : ℕ) [NeZero n] : CNF (Atom n) :=
  Encoding.latin .e1110 ++ Encoding.identities .e1110 ++
    Encoding.diagonal ++ Encoding.squares .e1110

def chain : CNF (Atom n) := all1 fun x => all1 fun y =>
  if x.val + 1 < y.val then ⟨#[[(p x x y, false)]]⟩ else .empty

def noTwoCycles : CNF (Atom n) := all1 fun x => all1 fun y =>
  if x ≠ y then ⟨#[[(p x x y, false), (p y y x, false)]]⟩ else .empty

def fixedDiagonal (d : Fin n → Fin n) : CNF (Atom n) :=
  all1 fun x => ⟨#[[(p x x (d x), true)]]⟩

def formula (n : ℕ) [NeZero n] : CNF (Atom n) :=
  base n ++ chain ++ noTwoCycles

def fixedFormula (d : Fin n → Fin n) : CNF (Atom n) := base n ++ fixedDiagonal d

def toNat (F : CNF (Atom n)) : CNF ℕ := sanitize (F.relabel code)

def natFormula (n : ℕ) [NeZero n] : CNF ℕ := toNat (formula n)

def fixedNat (d : Fin n → Fin n) : CNF ℕ := toNat (fixedFormula d)

lemma model_base (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) :
    (base n).Sat (meaning .e1110 f) := by
  simp only [base, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨Encoding.model_latin .e1110 f h, Encoding.model_identities .e1110 f h⟩,
    Encoding.model_diagonal .e1110 f hd⟩, Encoding.model_squares .e1110 f h⟩

omit [NeZero n] in
lemma model_chain (f : Fin n → Fin n → Fin n)
    (hc : ∀ x, (f x x).val ≤ x.val + 1) : chain.Sat (meaning .e1110 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  split
  · rename_i hxy
    apply sat_single
    have hn : f x x ≠ y := by
      intro he
      have hh := hc x
      rw [he] at hh
      omega
    simp [CNF.Clause.eval, meaning, p, hn]
  · exact CNF.sat_empty

omit [NeZero n] in
lemma model_noTwoCycles (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f) :
    noTwoCycles.Sat (meaning .e1110 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  split
  · rename_i hxy
    apply sat_single
    by_cases hx : f x x = y
    · have hy : f y y ≠ x := fun he => hxy (square_two_cycle h hx he)
      simp [CNF.Clause.eval, meaning, p, hy]
    · simp [CNF.Clause.eval, meaning, p, hx]
  · exact CNF.sat_empty

lemma model_fixed (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (d : Fin n → Fin n)
    (hD : ∀ x, f x x = d x) : (fixedFormula d).Sat (meaning .e1110 f) := by
  apply sat_append
  · exact model_base f h hd
  · apply sat_all1; intro x
    apply sat_single
    simp [CNF.Clause.eval, meaning, p, hD]

lemma unsat_of_toNat_unsat {F : CNF (Atom n)} (hn : (toNat F).Unsat) : F.Unsat := by
  have raw : (F.relabel code).Unsat := by
    intro a
    cases he : ((F.relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (toNat F).Sat a := by
        simp only [CNF.Sat, CNF.eval, toNat, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  exact (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp raw

theorem no_operation_fixed (d : Fin n → Fin n) (hn : (fixedNat d).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hD : ∀ x, f x x = d x) : False := by
  have hh := unsat_of_toNat_unsat hn (meaning .e1110 f)
  rw [model_fixed f h hd d hD] at hh
  contradiction

theorem not_hasModel (hn : (natFormula n).Unsat) : ¬ Law1110.HasModel n := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf, hd, hc⟩ := SquareNormalization.normalized M.op
    ((holds_iff .e1110 M).mpr hM)
  have hm : (formula n).Sat (meaning .e1110 f) := by
    simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
    exact ⟨⟨model_base f hf hd, model_chain f hc⟩, model_noTwoCycles f hf⟩
  have hh := unsat_of_toNat_unsat hn (meaning .e1110 f)
  rw [hm] at hh
  contradiction

end Spectrum.E1110.SquareEncoding
