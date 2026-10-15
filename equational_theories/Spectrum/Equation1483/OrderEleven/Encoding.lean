import equational_theories.Definability.Central1483Normalization
import equational_theories.Spectrum.Equation1483.Graph

/-! The order-eleven encoding with explicit graph consequences and optional
fixed table entries. All extra clauses are consequences of E1483; the entries
are used only as exhaustive case distinctions. -/
namespace Spectrum.E1483.OrderEleven.Encoding
open Std.Sat Magma.Central1483.CNF

abbrev Cell := Fin 11 × Fin 11 × Fin 11

def transpose : CNF (Atom 11) := all1 fun a => all1 fun b =>
  ⟨#[[(row a b, false), (col b a, true)],
      [(col b a, false), (row a b, true)]]⟩

def paths : CNF (Atom 11) := all1 fun a => all1 fun b => all1 fun z =>
  ⟨#[[(p a b z, false), (row z b, true)],
      [(p a b z, false), (col z a, true)]]⟩

def units (cells : List Cell) : CNF (Atom 11) := allList cells fun c =>
  ⟨#[[(p c.1 c.2.1 c.2.2, true)]]⟩

def formula (k : Nat) (zero : Bool) (cells : List Cell) : CNF (Atom 11) :=
  rankFormula 11 k zero ++ transpose ++ paths ++ units cells

def toNat (k : Nat) (zero : Bool) (cells : List Cell) : CNF Nat :=
  sanitize ((formula k zero cells).relabel code)

lemma model_transpose (f : Fin 11 → Fin 11 → Fin 11)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    CNF.Sat (meaning f) transpose := by
  letI : Magma (Fin 11) := ⟨f⟩
  have he : Equation1483 (Fin 11) := fun x y z => (h x y z).symm
  apply sat_all1
  intro a
  apply sat_all1
  intro b
  have hab : (∃ z, f a z = b) ↔ ∃ z, f z b = a := Graph.edge_iff_column he a b
  apply sat_two <;> by_cases hh : ∃ z, f a z = b <;>
    simp_all [CNF.Clause.eval, meaning, row, col]

lemma model_paths (f : Fin 11 → Fin 11 → Fin 11)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    CNF.Sat (meaning f) paths := by
  letI : Magma (Fin 11) := ⟨f⟩
  have he : Equation1483 (Fin 11) := fun x y z => (h x y z).symm
  apply sat_all1
  intro a
  apply sat_all1
  intro b
  apply sat_all1
  intro z
  have hr : ∃ w, f (f a b) w = b := (Graph.product_path he a b).2
  have hc : ∃ w, f w (f a b) = a :=
    (Graph.edge_iff_column he a (f a b)).mp ⟨b, rfl⟩
  apply sat_two <;> by_cases hz : f a b = z <;>
    simp_all [CNF.Clause.eval, meaning, p, row, col]

lemma model_units (f : Fin 11 → Fin 11 → Fin 11) (cells : List Cell)
    (h : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : CNF.Sat (meaning f) (units cells) := by
  apply sat_allList
  intro c hc
  apply sat_single
  simp [CNF.Clause.eval, meaning, p, h c hc]

lemma model_formula (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) (cells : List Cell)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) :
    CNF.Sat (meaning f) (formula k zero cells) := by
  exact sat_append _ _ _
    (sat_append _ _ _ (sat_append _ _ _ (model_rankFormula f k zero h)
      (model_transpose f h.source)) (model_paths f h.source)) (model_units f cells hc)

lemma no_model (k : Nat) (zero : Bool) (cells : List Cell)
    (hn : (toNat k zero cells).Unsat)
    (f : Fin 11 → Fin 11 → Fin 11) (h : RankAssumptions f k zero)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (formula k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code11_injective he)).mp
      (unsat_of_sanitize _ hn)
  have hh := hn' (meaning f)
  rw [model_formula f k zero h cells hc] at hh
  contradiction

end Spectrum.E1483.OrderEleven.Encoding
