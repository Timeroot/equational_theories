import equational_theories.Definability.Invariant
import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-!
The earlier 42-leaf candidate satisfies E3545 on this three-element E3342
model, but no term in that candidate operation recovers the source operation.
The obstruction is the candidate's closed subset `{0, 2}`. This rejects the
candidate term, not the general E3342/E3545 term-structural implication.
-/

namespace CubeCandidateRecovery

@[implicit_reducible] def source : Magma (Fin 3) where
  op := ![![0, 0, 1], ![0, 0, 1], ![1, 1, 2]]

def candidate (x y : Fin 3) : Fin 3 :=
  let f := source.op
  let u := f y x
  let a := f (f x x) (f y y)
  let b := f (f y y) (f x x)
  let c := f (f b u) (f u b)
  let d := f a (f (f (f u b) b) a)
  f (f d c) c

@[implicit_reducible] def target : Magma (Fin 3) := ⟨candidate⟩

theorem source_law : @Equation3342 (Fin 3) source := by decide

theorem target_law : @Equation3545 (Fin 3) target := by decide

theorem target_table : ∀ x y, target.op x y =
    (![![0, 0, 0], ![0, 0, 0], ![0, 0, 2]] : Fin 3 → Fin 3 → Fin 3) x y := by decide

private theorem target_closed : ∀ a b : Fin 3,
    (a = 0 ∨ a = 2) → (b = 0 ∨ b = 2) →
    target.op a b = 0 ∨ target.op a b = 2 := by decide

/-- Every binary target term takes `(0, 2)` back into `{0, 2}`. -/
private theorem target_invariant : target.IsCloneInvariant
    (fun f => f 0 2 = 0 ∨ f 0 2 = 2) where
  fst := Or.inl rfl
  snd := Or.inr rfl
  comp f g hf hg := target_closed (f 0 2) (g 0 2) hf hg

theorem no_term_recovery :
    ¬ @Set.TermDefinable _ ∅ MagmaLanguage target.FOStructure _ source.FinArityOp := by
  intro h
  have hh := target_invariant.of_termDefinable h
  have hn : ¬ (source.op 0 2 = 0 ∨ source.op 0 2 = 2) := by decide
  exact hn hh

/-- info: 'CubeCandidateRecovery.no_term_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_term_recovery

end CubeCandidateRecovery
