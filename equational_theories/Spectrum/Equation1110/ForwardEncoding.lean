import equational_theories.Spectrum.Equation1110.SquareEncoding
import equational_theories.Generated.FiniteImplicationSearch.theorems.Inverses1

/-! Use the already established finite implication E1110 → E8 to propagate
along the squaring permutation: `f x (d x) = x`. -/
namespace Spectrum.E1110.ForwardEncoding
open Std.Sat SmallOrders
open SmallOrders.Encoding (Atom p meaning)
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append)
variable {n : ℕ} [NeZero n]

lemma forward_identity {A : Type*} [Finite A] (f : A → A → A)
    (h : Holds .e1110 f) (x : A) : f x (f x x) = x := by
  letI : Magma A := ⟨f⟩
  have hh : Equation1110 A := fun x y => (h x y).symm
  exact (Finite.Equation1110_implies_Equation8 A hh x).symm

def forward (d : Fin n → Fin n) : CNF (Atom n) :=
  all1 fun x => ⟨#[[(p x (d x) x,true)]]⟩

def forwardFormula (d : Fin n → Fin n) : CNF (Atom n) :=
  SquareEncoding.fixedFormula d ++ forward d

def forwardNat (d : Fin n → Fin n) : CNF ℕ :=
  SquareEncoding.toNat (forwardFormula d)

omit [NeZero n] in
lemma model_forward (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (d : Fin n → Fin n) (hD : ∀ x, f x x = d x) :
    (forward d).Sat (meaning .e1110 f) := by
  apply sat_all1; intro x
  apply sat_single
  have he : f x (d x) = x := by simpa [hD] using forward_identity f h x
  simp [CNF.Clause.eval,meaning,p,he]

lemma model_forwardFormula (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (d : Fin n → Fin n)
    (hD : ∀ x, f x x = d x) :
    (forwardFormula d).Sat (meaning .e1110 f) :=
  sat_append _ _ _ (SquareEncoding.model_fixed f h hd d hD) (model_forward f h d hD)

theorem no_operation_forward (d : Fin n → Fin n) (hn : (forwardNat d).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hD : ∀ x, f x x = d x) : False := by
  have hh := SquareEncoding.unsat_of_toNat_unsat hn (meaning .e1110 f)
  rw [model_forwardFormula f h hd d hD] at hh
  contradiction


/-- The simultaneous diagonal/row normalization used for a lone three-cycle. -/
def rowChainFormula (d : Fin n → Fin n) : CNF (Atom n) :=
  Encoding.formula .e1110 n ++ SquareEncoding.fixedDiagonal d ++ forward d

def rowChainNat (d : Fin n → Fin n) : CNF ℕ :=
  SquareEncoding.toNat (rowChainFormula d)

lemma model_rowChain (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (d : Fin n → Fin n) (hD : ∀ x, f x x = d x) :
    (rowChainFormula d).Sat (meaning .e1110 f) := by
  apply sat_append
  · apply sat_append
    · exact Encoding.model_formula .e1110 f h hd hc
    · apply sat_all1; intro x
      apply sat_single
      simp [CNF.Clause.eval,meaning,p,hD]
  · exact model_forward f h d hD

theorem no_operation_rowChain (d : Fin n → Fin n) (hn : (rowChainNat d).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hD : ∀ x, f x x = d x) : False := by
  have hh := SquareEncoding.unsat_of_toNat_unsat hn (meaning .e1110 f)
  rw [model_rowChain f h hd hc d hD] at hh
  contradiction

/-- A row-chain with additional room for a fixed initial block of labels. -/
def slackChain (k : ℕ) : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + k < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty

def slackFormula (d : Fin n → Fin n) (k : ℕ) : CNF (Atom n) :=
  forwardFormula d ++ slackChain k

def slackNat (d : Fin n → Fin n) (k : ℕ) : CNF ℕ :=
  SquareEncoding.toNat (slackFormula d k)

lemma model_slackChain (f : Fin n → Fin n → Fin n) (k : ℕ)
    (hc : ∀ y, (f 0 y).val ≤ y.val + k) :
    (slackChain k).Sat (meaning .e1110 f) := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hz
    apply sat_single
    have he : f 0 y ≠ z := by intro he; have := congrArg Fin.val he; have := hc y; omega
    simp [CNF.Clause.eval, meaning, p, he]
  · exact CNF.sat_empty

lemma model_slackFormula (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (d : Fin n → Fin n)
    (hD : ∀ x, f x x = d x) (k : ℕ) (hc : ∀ y, (f 0 y).val ≤ y.val + k) :
    (slackFormula d k).Sat (meaning .e1110 f) :=
  sat_append _ _ _ (model_forwardFormula f h hd d hD) (model_slackChain f k hc)

theorem no_operation_slack (d : Fin n → Fin n) (k : ℕ) (hn : (slackNat d k).Unsat)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hd : f 0 0 = 0 → ∀ x, f x x = x) (hc : ∀ y, (f 0 y).val ≤ y.val + k)
    (hD : ∀ x, f x x = d x) : False := by
  have hh := SquareEncoding.unsat_of_toNat_unsat hn (meaning .e1110 f)
  rw [model_slackFormula f h hd d hD k hc] at hh
  contradiction

end Spectrum.E1110.ForwardEncoding
