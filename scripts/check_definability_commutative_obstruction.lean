import equational_theories.Definability.CloneTraps
import Mathlib.Data.Fin.VecNotation

/-!
Neither E3342 nor E3545 uniformly supplies a commutative binary term.
These eight-element witnesses exclude all commutative terms, without a size bound.
They do not exclude arbitrary E4405 terms: E4405 also has noncommutative models.
-/

namespace CommutativeObstruction

private def flip : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

private theorem flip_ne : ∀ x, flip x ≠ x := by decide

private theorem invariant (M : Magma (Fin 8))
    (hm : ∀ x y, M.op (flip x) (flip y) = flip (M.op x y)) :
    M.IsCloneInvariant (fun f => ∀ x y, f (flip x) (flip y) = flip (f x y)) where
  fst _ _ := rfl
  snd _ _ := rfl
  comp f g hf hg x y := by
    change M.op (f (flip x) (flip y)) (g (flip x) (flip y)) = _
    rw [hf, hg, hm]

private theorem obstruction (M : Magma (Fin 8))
    (hm : ∀ x y, M.op (flip x) (flip y) = flip (M.op x y))
    (N : Magma (Fin 8))
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ N.FinArityOp) :
    ¬ ∀ x y, N.op x y = N.op y x := by
  intro hc
  have h := (invariant M hm).of_termDefinable ht 0 1
  change N.op 1 0 = flip (N.op 0 1) at h
  rw [hc 1 0] at h
  exact flip_ne _ h.symm

@[implicit_reducible] def source3342 : Magma (Fin 8) where
  op x y := (![![2, 1, 4, 3, 2, 0, 0, 7],
    ![0, 3, 2, 5, 1, 3, 6, 1],
    ![0, 6, 1, 1, 4, 2, 1, 0],
    ![7, 1, 0, 0, 3, 5, 1, 0],
    ![2, 0, 0, 7, 2, 1, 4, 3],
    ![1, 3, 6, 1, 0, 3, 2, 5],
    ![4, 2, 1, 0, 0, 6, 1, 1],
    ![3, 5, 1, 0, 7, 1, 0, 0]] : Fin 8 → Fin 8 → Fin 8) x y

theorem source3342_law : @Equation3342 (Fin 8) source3342 := by decide

private theorem source3342_flip :
    ∀ x y, source3342.op (flip x) (flip y) = flip (source3342.op x y) := by decide

theorem source3342_no_commutative_term (N : Magma (Fin 8))
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source3342.FOStructure _ N.FinArityOp) :
    ¬ ∀ x y, N.op x y = N.op y x := obstruction source3342 source3342_flip N ht

/-- info: 'CommutativeObstruction.source3342_no_commutative_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source3342_no_commutative_term

@[implicit_reducible] def source3545 : Magma (Fin 8) where
  op x y := (![![5, 1, 5, 0, 7, 0, 2, 4],
    ![0, 4, 1, 4, 1, 6, 5, 3],
    ![5, 0, 5, 1, 4, 2, 0, 7],
    ![1, 4, 0, 4, 3, 5, 6, 1],
    ![4, 3, 7, 1, 0, 1, 0, 0],
    ![2, 5, 0, 6, 0, 1, 1, 1],
    ![0, 6, 2, 5, 1, 1, 1, 0],
    ![7, 1, 4, 3, 0, 0, 1, 0]] : Fin 8 → Fin 8 → Fin 8) x y

theorem source3545_law : @Equation3545 (Fin 8) source3545 := by decide

private theorem source3545_flip :
    ∀ x y, source3545.op (flip x) (flip y) = flip (source3545.op x y) := by decide

theorem source3545_no_commutative_term (N : Magma (Fin 8))
    (ht : @Set.TermDefinable _ ∅ MagmaLanguage source3545.FOStructure _ N.FinArityOp) :
    ¬ ∀ x y, N.op x y = N.op y x := obstruction source3545 source3545_flip N ht

/-- info: 'CommutativeObstruction.source3545_no_commutative_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source3545_no_commutative_term

end CommutativeObstruction
