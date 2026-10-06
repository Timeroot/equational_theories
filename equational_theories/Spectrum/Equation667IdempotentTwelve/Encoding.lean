import equational_theories.Spectrum.Equation63.OrderTen.Encoding
import equational_theories.Spectrum.Equation667883Small.Basic

/-! The idempotent E667 exclusion reuses the simpler E229 cubic encoding.
Both the change of operation and the symmetry reduction preserve idempotency. -/

namespace Spectrum.E667.IdempotentTwelve
open Std.Sat E63.OrderTen E63.OrderTen.Encoding
variable {n : ℕ} [NeZero n]

def idem (n : ℕ) : CNF (Atom n) := all1 fun x => ⟨#[[(p x x x, true)]]⟩
def formula (n : ℕ) [NeZero n] : CNF (Atom n) := Encoding.formula n ++ idem n
def natFormula (n : ℕ) [NeZero n] : CNF ℕ := sanitize ((formula n).relabel code)

private theorem code_inj : Function.Injective (@code n) := by
  have digits {a b c d : ℕ} (hc : c < n) (hd : d < n) (he : a*n+c = b*n+d) :
      a = b ∧ c = d := by
    have ht := congrArg (fun t => t % n) he
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at ht
    exact ⟨Nat.eq_of_mul_eq_mul_right (NeZero.pos n) (by omega), ht⟩
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ he
  obtain ⟨he,hz⟩ := digits z.isLt z'.isLt he
  obtain ⟨hx,hy⟩ := digits y.isLt y'.isLt he
  exact Prod.ext (Fin.ext hx) (Prod.ext (Fin.ext hy) (Fin.ext hz))

private theorem unsat_of_sanitized {α : Type} (F : CNF α) (c : α → ℕ)
    (hc : Function.Injective c) (hn : (sanitize (F.relabel c)).Unsat) : F.Unsat := by
  have raw : (F.relabel c).Unsat := by
    intro a
    cases he : (F.relabel c).eval a with
    | false => rfl
    | true =>
      have hs : (sanitize (F.relabel c)).Sat a := by
        simp only [CNF.Sat, CNF.eval, sanitize,
          Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun cl hcl => he cl (Array.mem_filter.mp hcl).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  exact (CNF.unsat_relabel_iff (fun _ _ he => hc he)).mp raw

private theorem unsat_append_left {α : Type} (F G : CNF α) (m : α → Bool)
    (hn : (F ++ G).Unsat) (hF : F.Sat m) (hG : G.Sat m) : False := by
  have hm := sat_append m F G hF hG
  have hh := hn m
  rw [hm] at hh
  contradiction

theorem no_normalized_model (hn : (natFormula n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Cubic f) (hi : ∀ x, f x x = x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : False := by
  have hid : (idem n).Sat (meaning f) := by
    refine sat_all1 (meaning f) (fun x => ⟨#[[(p x x x, true)]]⟩) ?_
    intro x
    apply sat_single
    simp [CNF.Clause.eval, meaning, hi]
  exact unsat_append_left (Encoding.formula n) (idem n) (meaning f)
    (unsat_of_sanitized (formula n) code code_inj hn)
    (model_formula f h (fun _ => hi) hc) hid

theorem no_cubic_model (hn : (natFormula n).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Cubic f) (hi : ∀ x, f x x = x) : False := by
  obtain ⟨e, he, hc⟩ := exists_chain_label (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let g (x y : Fin n) := e (f (e.symm x) (e.symm y))
  apply no_normalized_model hn g (cubic_relabel h e)
  · intro x
    simp only [g, hi, Equiv.apply_symm_apply]
  · intro y
    simpa only [g, he'] using hc y

theorem no_idempotent_e667 (hn : (natFormula n).Unsat) [Magma (Fin n)]
    (h : Equation667 (Fin n)) (hi : ∀ x : Fin n, x ◇ x = x) : False := by
  let d (x y : Fin n) := y ◇ (y ◇ x)
  have hd (x y : Fin n) : x ◇ d x y = y := by
    simpa only [d, hi] using (h y x).symm
  have cubic : Cubic d := by
    intro x y
    change x ◇ (x ◇ d x (d x y)) = y
    rw [hd, hd]
  exact no_cubic_model hn d cubic (fun x => by simp only [d, hi])

end Spectrum.E667.IdempotentTwelve
