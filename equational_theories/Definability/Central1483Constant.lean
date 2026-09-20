import equational_theories.Equations.All
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite

/-! Replayed equational proofs for E1483 with a constant row. -/

namespace CentralConstant
variable {G : Type*} [Magma G]

/- BEGIN REPLAYED PROOFS -/
theorem left_six (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (x : G)  :
    (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x)))))) = x := by
  have dual (a b c : G) : ((c ◇ b) ◇ a) ◇ (a ◇ b) = a := by
    calc
      ((c ◇ b) ◇ a) ◇ (a ◇ b) =
          ((c ◇ b) ◇ a) ◇ (a ◇ ((c ◇ b) ◇ (b ◇ (c ◇ b)))) :=
        congrArg (fun t => ((c ◇ b) ◇ a) ◇ (a ◇ t)) (h b c b)
      _ = a := (h a (c ◇ b) (b ◇ (c ◇ b))).symm
  have axiom_1 (v_X : G) : (zero ◇ v_X) = one := by
    exact hzero v_X
  have axiom_2 (v_X v_Y v_Z : G) : ((v_X ◇ v_Y) ◇ (v_Y ◇ (v_X ◇ v_Z))) = v_Y := by
    exact (h v_Y v_X v_Z).symm
  have axiom_3 (v_X v_Y v_Z : G) : (((v_X ◇ v_Y) ◇ v_Z) ◇ (v_Z ◇ v_Y)) = v_Z := by
    exact dual v_Z v_Y v_X
  have lemma_4 (v_X : G) : (one ◇ (v_X ◇ one)) = v_X := by
    calc
      (one ◇ (v_X ◇ one)) = (one ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (one ◇ (v_X ◇ hole))) (axiom_1 zero).symm
      _ = ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (hole ◇ (v_X ◇ (zero ◇ zero)))) (axiom_1 v_X).symm
      _ = v_X := (axiom_2 zero v_X zero)
  have lemma_5 (v_X : G) : (v_X ◇ zero) = one := by
    calc
      (v_X ◇ zero) = (one ◇ ((v_X ◇ zero) ◇ one)) := (lemma_4 (v_X ◇ zero)).symm
      _ = (one ◇ ((v_X ◇ zero) ◇ (zero ◇ (v_X ◇ zero)))) := congrArg (fun hole : G => (one ◇ ((v_X ◇ zero) ◇ hole))) (axiom_1 (v_X ◇ zero)).symm
      _ = (one ◇ zero) := congrArg (fun hole : G => (one ◇ hole)) (axiom_2 v_X zero zero)
      _ = (one ◇ (one ◇ (zero ◇ one))) := congrArg (fun hole : G => (one ◇ hole)) (lemma_4 zero).symm
      _ = (one ◇ (one ◇ one)) := congrArg (fun hole : G => (one ◇ (one ◇ hole))) (axiom_1 one)
      _ = one := (lemma_4 one)
  have lemma_6 (v_W v_X v_Y v_Z : G) : (v_X ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W))) = (v_X ◇ (v_Y ◇ v_Z)) := by
    calc
      (v_X ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W))) = (((v_Y ◇ v_X) ◇ (v_X ◇ (v_Y ◇ v_Z))) ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W))) := congrArg (fun hole : G => (hole ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W)))) (axiom_2 v_Y v_X v_Z).symm
      _ = (v_X ◇ (v_Y ◇ v_Z)) := (axiom_2 (v_Y ◇ v_X) (v_X ◇ (v_Y ◇ v_Z)) v_W)
  have lemma_7 (v_X : G) : ((one ◇ v_X) ◇ one) = v_X := by
    calc
      ((one ◇ v_X) ◇ one) = ((one ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((one ◇ v_X) ◇ hole)) (lemma_5 v_X).symm
      _ = (((zero ◇ zero) ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((hole ◇ v_X) ◇ (v_X ◇ zero))) (lemma_5 zero).symm
      _ = v_X := (axiom_3 zero zero v_X)
  have lemma_8 (v_X v_Y v_Z : G) : ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z)) = (v_X ◇ v_Y) := by
    calc
      ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z)) = ((one ◇ ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z))) ◇ one) := (lemma_7 ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z))).symm
      _ = ((one ◇ (v_X ◇ v_Y)) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (lemma_6 v_Z one v_X v_Y)
      _ = (v_X ◇ v_Y) := (lemma_7 (v_X ◇ v_Y))
  have lemma_9 (v_W v_X v_Y v_Z : G) : (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ v_Y) = (v_Z ◇ v_Y) := by
    calc
      (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ v_Y) = (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ ((v_Z ◇ v_Y) ◇ (v_Y ◇ (v_Z ◇ v_W)))) := congrArg (fun hole : G => (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ hole)) (axiom_2 v_Z v_Y v_W).symm
      _ = (v_Z ◇ v_Y) := (axiom_3 v_X (v_Y ◇ (v_Z ◇ v_W)) (v_Z ◇ v_Y))
  have lemma_10 (v_X v_Y v_Z : G) : ((v_X ◇ (one ◇ v_Y)) ◇ ((v_Z ◇ v_Y) ◇ one)) = (v_Z ◇ v_Y) := by
    calc
      ((v_X ◇ (one ◇ v_Y)) ◇ ((v_Z ◇ v_Y) ◇ one)) = ((v_X ◇ (one ◇ ((v_Z ◇ v_Y) ◇ (v_Y ◇ (v_Z ◇ zero))))) ◇ ((v_Z ◇ v_Y) ◇ one)) := congrArg (fun hole : G => ((v_X ◇ (one ◇ hole)) ◇ ((v_Z ◇ v_Y) ◇ one))) (axiom_2 v_Z v_Y zero).symm
      _ = (one ◇ (((v_X ◇ (one ◇ ((v_Z ◇ v_Y) ◇ (v_Y ◇ (v_Z ◇ zero))))) ◇ ((v_Z ◇ v_Y) ◇ one)) ◇ one)) := (lemma_4 ((v_X ◇ (one ◇ ((v_Z ◇ v_Y) ◇ (v_Y ◇ (v_Z ◇ zero))))) ◇ ((v_Z ◇ v_Y) ◇ one))).symm
      _ = (one ◇ ((v_Z ◇ v_Y) ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (lemma_9 (v_Y ◇ (v_Z ◇ zero)) v_X one (v_Z ◇ v_Y))
      _ = (v_Z ◇ v_Y) := (lemma_4 (v_Z ◇ v_Y))
  have lemma_11 (v_X v_Y v_Z : G) : ((v_X ◇ v_Y) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one)) = (v_Z ◇ (v_Y ◇ one)) := by
    calc
      ((v_X ◇ v_Y) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one)) = ((v_X ◇ (one ◇ (v_Y ◇ one))) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one)) := congrArg (fun hole : G => ((v_X ◇ hole) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one))) (lemma_4 v_Y).symm
      _ = (v_Z ◇ (v_Y ◇ one)) := (lemma_10 v_X (v_Y ◇ one) v_Z)
  have lemma_12 (v_X v_Y v_Z : G) : ((v_X ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ v_Z) ◇ one)) = (v_Y ◇ v_Z) := by
    calc
      ((v_X ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ v_Z) ◇ one)) = ((v_X ◇ (v_Y ◇ one)) ◇ (((one ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ one) ◇ one)) ◇ one)) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ one)) ◇ (hole ◇ one))) (lemma_8 v_Y v_Z one).symm
      _ = ((one ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ one) ◇ one)) := (lemma_11 v_X (v_Y ◇ one) (one ◇ (v_Y ◇ v_Z)))
      _ = (v_Y ◇ v_Z) := (lemma_8 v_Y v_Z one)
  have lemma_13 (v_X v_Y : G) : (v_X ◇ (v_Y ◇ one)) = (v_X ◇ (v_Y ◇ v_X)) := by
    calc
      (v_X ◇ (v_Y ◇ one)) = (v_X ◇ ((v_X ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ v_X) ◇ one))) := (lemma_6 one v_X v_Y one).symm
      _ = (v_X ◇ (v_Y ◇ v_X)) := congrArg (fun hole : G => (v_X ◇ hole)) (lemma_12 v_X v_Y v_X)
  have lemma_14 (v_X v_Y : G) : ((v_X ◇ (v_Y ◇ v_X)) ◇ v_X) = (v_Y ◇ v_X) := by
    calc
      ((v_X ◇ (v_Y ◇ v_X)) ◇ v_X) = ((v_X ◇ (v_Y ◇ v_X)) ◇ ((v_Y ◇ v_X) ◇ (v_X ◇ (v_Y ◇ zero)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_X)) ◇ hole)) (axiom_2 v_Y v_X zero).symm
      _ = (v_Y ◇ v_X) := (axiom_2 v_X (v_Y ◇ v_X) (v_Y ◇ zero))
  have lemma_15 (v_X v_Y : G) : ((one ◇ v_X) ◇ v_Y) = ((v_Y ◇ v_X) ◇ v_Y) := by
    calc
      ((one ◇ v_X) ◇ v_Y) = ((v_Y ◇ ((one ◇ v_X) ◇ v_Y)) ◇ v_Y) := (lemma_14 v_Y (one ◇ v_X)).symm
      _ = ((v_Y ◇ ((one ◇ v_X) ◇ one)) ◇ v_Y) := congrArg (fun hole : G => (hole ◇ v_Y)) (lemma_13 v_Y (one ◇ v_X)).symm
      _ = ((v_Y ◇ v_X) ◇ v_Y) := congrArg (fun hole : G => ((v_Y ◇ hole) ◇ v_Y)) (lemma_7 v_X)
  have lemma_16 (v_X v_Y v_Z : G) : ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (v_X ◇ v_Z)) = ((one ◇ v_X) ◇ v_Y) := by
    calc
      ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (v_X ◇ v_Z)) = ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (((one ◇ v_X) ◇ one) ◇ v_Z)) := congrArg (fun hole : G => ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (hole ◇ v_Z))) (lemma_7 v_X).symm
      _ = ((one ◇ v_X) ◇ v_Y) := (lemma_8 (one ◇ v_X) v_Y v_Z)
  have lemma_17 (v_X v_Y v_Z : G) : (v_X ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ v_X)) = (v_Y ◇ ((v_X ◇ v_Z) ◇ one)) := by
    calc
      (v_X ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ v_X)) = (v_X ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ one)) := (lemma_13 v_X (v_Y ◇ ((v_X ◇ v_Z) ◇ one))).symm
      _ = ((((zero ◇ v_Z) ◇ v_X) ◇ (v_X ◇ v_Z)) ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ one)) := congrArg (fun hole : G => (hole ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ one))) (axiom_3 zero v_Z v_X).symm
      _ = (v_Y ◇ ((v_X ◇ v_Z) ◇ one)) := (lemma_11 ((zero ◇ v_Z) ◇ v_X) (v_X ◇ v_Z) v_Y)
  have lemma_18 (v_X v_Y v_Z : G) : (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ v_Y)) ◇ (v_X ◇ (v_Y ◇ one))) = (v_Z ◇ v_Y) := by
    calc
      (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ v_Y)) ◇ (v_X ◇ (v_Y ◇ one))) = (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ (one ◇ (v_Y ◇ one)))) ◇ (v_X ◇ (v_Y ◇ one))) := congrArg (fun hole : G => (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ hole)) ◇ (v_X ◇ (v_Y ◇ one)))) (lemma_4 v_Y).symm
      _ = (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ (one ◇ (v_Y ◇ one)))) ◇ ((v_Z ◇ (one ◇ (v_Y ◇ one))) ◇ ((v_X ◇ (v_Y ◇ one)) ◇ one))) := congrArg (fun hole : G => (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ (one ◇ (v_Y ◇ one)))) ◇ hole)) (lemma_10 v_Z (v_Y ◇ one) v_X).symm
      _ = (v_Z ◇ (one ◇ (v_Y ◇ one))) := (axiom_2 (v_X ◇ (v_Y ◇ one)) (v_Z ◇ (one ◇ (v_Y ◇ one))) one)
      _ = (v_Z ◇ v_Y) := congrArg (fun hole : G => (v_Z ◇ hole)) (lemma_4 v_Y)
  have lemma_19 (v_X v_Y v_Z : G) : ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (v_X ◇ one))) = ((v_X ◇ (v_Y ◇ v_Z)) ◇ v_Z) := by
    calc
      ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (v_X ◇ one))) = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ hole))) (lemma_7 (v_X ◇ one)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_13 (one ◇ v_Z) (one ◇ (v_X ◇ one)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ hole))) (lemma_9 (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) one (one ◇ v_Z) (one ◇ (v_X ◇ one))).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (((one ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (hole ◇ (one ◇ v_Z))))) (lemma_16 ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) one).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_17 (one ◇ v_Z) (one ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_16 ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) one)
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one)) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ hole) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_12 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z) ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z)
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ hole) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_13 (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one)))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ hole)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_13 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ hole))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_13 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ hole))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (axiom_2 (one ◇ (v_X ◇ one)) (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))) (v_Y ◇ v_Z)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ◇ hole)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_14 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ hole)) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (axiom_2 (one ◇ v_Z) ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ hole))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_13 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z)
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ hole) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_13 (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) (one ◇ (v_X ◇ one))).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_15 ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one)) ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ hole))) (lemma_8 (one ◇ (v_X ◇ one)) (one ◇ v_Z) one).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((hole ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one))))) (lemma_8 (one ◇ (v_X ◇ one)) (one ◇ v_Z) one).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_18 (one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ((one ◇ (v_X ◇ one)) ◇ one) (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ hole))) (lemma_7 (v_X ◇ one))
      _ = (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((hole ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (lemma_4 v_X).symm
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => (hole ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (lemma_15 (v_X ◇ one) (v_Y ◇ v_Z))
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((hole ◇ v_Z) ◇ (v_X ◇ one)))) (lemma_15 (v_X ◇ one) (v_Y ◇ v_Z))
      _ = ((((v_Y ◇ v_Z) ◇ (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => (hole ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (axiom_3 v_Y v_Z (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))).symm
      _ = ((((((zero ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_Z) ◇ (v_X ◇ one))) ◇ (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => (((hole ◇ (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (axiom_3 zero (v_X ◇ one) (v_Y ◇ v_Z)).symm
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((hole ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (axiom_3 (zero ◇ (v_X ◇ one)) (v_Y ◇ v_Z) ((v_Y ◇ v_Z) ◇ (v_X ◇ one)))
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) := (axiom_3 (v_Y ◇ v_Z) (v_X ◇ one) ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))
      _ = (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) := congrArg (fun hole : G => (hole ◇ v_Z)) (lemma_15 (v_X ◇ one) (v_Y ◇ v_Z)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ v_Z) := congrArg (fun hole : G => ((hole ◇ (v_Y ◇ v_Z)) ◇ v_Z)) (lemma_4 v_X)
  have lemma_20 (v_X v_Y v_Z : G) : ((one ◇ v_X) ◇ (v_Y ◇ (v_Z ◇ v_X))) = ((one ◇ v_X) ◇ (v_Y ◇ one)) := by
    calc
      ((one ◇ v_X) ◇ (v_Y ◇ (v_Z ◇ v_X))) = (((v_Y ◇ (v_Z ◇ v_X)) ◇ v_X) ◇ (v_Y ◇ (v_Z ◇ v_X))) := (lemma_15 v_X (v_Y ◇ (v_Z ◇ v_X)))
      _ = (((v_Y ◇ (v_Z ◇ v_X)) ◇ v_X) ◇ ((one ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ (v_Z ◇ v_X)) ◇ one))) := congrArg (fun hole : G => (((v_Y ◇ (v_Z ◇ v_X)) ◇ v_X) ◇ hole)) (lemma_12 one v_Y (v_Z ◇ v_X)).symm
      _ = (((v_Y ◇ (v_Z ◇ v_X)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ ((one ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ (v_Z ◇ v_X)) ◇ one))) := congrArg (fun hole : G => (hole ◇ ((one ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ (v_Z ◇ v_X)) ◇ one)))) (lemma_19 v_Y v_Z v_X).symm
      _ = (((v_Y ◇ (v_Z ◇ v_X)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one)) := (lemma_19 (v_Y ◇ (v_Z ◇ v_X)) (one ◇ v_X) (v_Y ◇ one))
      _ = ((((one ◇ (v_Y ◇ (v_Z ◇ v_X))) ◇ ((v_Y ◇ one) ◇ one)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one)) := congrArg (fun hole : G => ((hole ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one))) (lemma_8 v_Y (v_Z ◇ v_X) one).symm
      _ = ((((one ◇ (v_Y ◇ (v_Z ◇ v_X))) ◇ ((v_Y ◇ one) ◇ ((one ◇ v_X) ◇ zero))) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one)) := congrArg (fun hole : G => ((((one ◇ (v_Y ◇ (v_Z ◇ v_X))) ◇ ((v_Y ◇ one) ◇ hole)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one))) (lemma_5 (one ◇ v_X)).symm
      _ = ((one ◇ v_X) ◇ (v_Y ◇ one)) := (lemma_9 zero (one ◇ (v_Y ◇ (v_Z ◇ v_X))) (v_Y ◇ one) (one ◇ v_X))
  have lemma_21 (v_X v_Y v_Z : G) : ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z)) = v_X := by
    calc
      ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z)) = ((one ◇ ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))) ◇ one) := (lemma_7 ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))).symm
      _ = (((((v_Y ◇ v_X) ◇ one) ◇ (one ◇ v_X)) ◇ ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))) ◇ one) := congrArg (fun hole : G => ((hole ◇ ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))) ◇ one)) (axiom_3 v_Y v_X one).symm
      _ = ((one ◇ v_X) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (axiom_2 ((v_Y ◇ v_X) ◇ one) (one ◇ v_X) v_Z)
      _ = v_X := (lemma_7 v_X)
  have lemma_22 (v_X v_Y v_Z : G) : ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ v_X)) = one := by
    calc
      ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ v_X)) = ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (((zero ◇ (one ◇ v_Y)) ◇ v_X) ◇ (v_X ◇ (one ◇ v_Y))))) := congrArg (fun hole : G => ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ hole))) (axiom_3 zero (one ◇ v_Y) v_X).symm
      _ = ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) := (lemma_20 (v_X ◇ (one ◇ v_Y)) (v_Y ◇ v_Z) ((zero ◇ (one ◇ v_Y)) ◇ v_X))
      _ = ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y))))) := (lemma_20 (v_X ◇ (one ◇ v_Y)) (v_Y ◇ v_Z) one).symm
      _ = ((one ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ ((v_X ◇ (one ◇ v_Y)) ◇ ((one ◇ v_Y) ◇ (v_X ◇ zero)))) := (lemma_16 (v_X ◇ (one ◇ v_Y)) ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))) ((one ◇ v_Y) ◇ (v_X ◇ zero))).symm
      _ = ((one ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => ((one ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ hole)) (axiom_2 v_X (one ◇ v_Y) zero)
      _ = (((one ◇ v_Y) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ (one ◇ v_Y)) := (lemma_15 ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y))))) (one ◇ v_Y))
      _ = (((one ◇ v_Y) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (((one ◇ v_Y) ◇ hole) ◇ (one ◇ v_Y))) (lemma_13 (one ◇ (v_X ◇ (one ◇ v_Y))) (v_Y ◇ v_Z)).symm
      _ = (((((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) ◇ v_Y) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (lemma_15 v_Y ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)))
      _ = (((((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) ◇ (((zero ◇ v_Z) ◇ v_Y) ◇ (v_Y ◇ v_Z))) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (((((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) ◇ hole) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y))) (axiom_3 zero v_Z v_Y).symm
      _ = ((((zero ◇ v_Z) ◇ v_Y) ◇ (v_Y ◇ v_Z)) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (lemma_18 (one ◇ (v_X ◇ (one ◇ v_Y))) (v_Y ◇ v_Z) ((zero ◇ v_Z) ◇ v_Y))
      _ = (v_Y ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (axiom_3 zero v_Z v_Y)
      _ = (((one ◇ v_Y) ◇ one) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (lemma_7 v_Y).symm
      _ = one := (axiom_3 one v_Y one)
  have lemma_23 (v_X v_Y v_Z : G) : (((v_X ◇ v_Y) ◇ (v_Z ◇ (v_X ◇ v_Z))) ◇ (v_X ◇ one)) = (v_Z ◇ (v_X ◇ v_Z)) := by
    calc
      (((v_X ◇ v_Y) ◇ (v_Z ◇ (v_X ◇ v_Z))) ◇ (v_X ◇ one)) = (((v_X ◇ v_Y) ◇ (v_Z ◇ (v_X ◇ one))) ◇ (v_X ◇ one)) := congrArg (fun hole : G => (((v_X ◇ v_Y) ◇ hole) ◇ (v_X ◇ one))) (lemma_13 v_Z v_X).symm
      _ = ((((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ (v_Z ◇ zero))) ◇ (v_Z ◇ (v_X ◇ one))) ◇ (v_X ◇ one)) := congrArg (fun hole : G => ((hole ◇ (v_Z ◇ (v_X ◇ one))) ◇ (v_X ◇ one))) (lemma_8 v_X v_Y (v_Z ◇ zero)).symm
      _ = (v_Z ◇ (v_X ◇ one)) := (lemma_9 zero (one ◇ (v_X ◇ v_Y)) (v_X ◇ one) v_Z)
      _ = (v_Z ◇ (v_X ◇ v_Z)) := (lemma_13 v_Z v_X)
  calc
    (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x)))))) = (one ◇ (one ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ one) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ hole))) (lemma_21 (one ◇ (one ◇ (one ◇ (one ◇ x)))) one one).symm
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ zero) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)))) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ one)) ◇ (((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ one) ◇ one)) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ hole))) (lemma_11 (((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ zero) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)))) ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ one) (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x)))))).symm
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ zero) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)))) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ one)) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ zero) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)))) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ one)) ◇ (hole ◇ one))))) (lemma_21 (one ◇ (one ◇ (one ◇ (one ◇ x)))) one one)
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one))) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ (hole ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one))))) (lemma_23 (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) zero (((one ◇ (one ◇ x)) ◇ one) ◇ one))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ hole) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one))))) (lemma_22 one (one ◇ (one ◇ x)) one)
    _ = (one ◇ (one ◇ ((one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one)) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ (hole ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ one))))) (lemma_4 ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)).symm
    _ = (one ◇ (one ◇ ((one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one)) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ (((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ zero) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x)))))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one)))))) := congrArg (fun hole : G => (one ◇ (one ◇ hole))) (lemma_20 (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one) (one ◇ (one ◇ (one ◇ (one ◇ x)))) ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ zero) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x))))))).symm
    _ = (one ◇ (one ◇ ((one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one)) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x))))))))) := congrArg (fun hole : G => (one ◇ (one ◇ ((one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one)) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ hole))))) (lemma_23 ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) zero (one ◇ (one ◇ (one ◇ x))))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x))))))))) := congrArg (fun hole : G => (one ◇ (one ◇ (hole ◇ ((one ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x)))))))))) (lemma_4 ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((one ◇ one) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x))))) ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x))))))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((hole ◇ (one ◇ (one ◇ (one ◇ x)))) ◇ ((one ◇ (one ◇ (one ◇ x))) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x)))))))))) (lemma_21 one ((one ◇ (one ◇ x)) ◇ one) (one ◇ (one ◇ (one ◇ x)))).symm
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ hole)))) (axiom_3 (one ◇ one) (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ (one ◇ (one ◇ x)))) (one ◇ (one ◇ (one ◇ x))))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (one ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one))) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (hole ◇ (one ◇ (one ◇ x))))))) (axiom_2 (((one ◇ (one ◇ x)) ◇ one) ◇ one) one one).symm
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ hole) ◇ (one ◇ (one ◇ x))))))) (lemma_4 (((one ◇ (one ◇ x)) ◇ one) ◇ one))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (((one ◇ ((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one))) ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one))))) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ hole) ◇ (one ◇ (one ◇ x))))))) (axiom_3 one ((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one)) (((one ◇ (one ◇ x)) ◇ one) ◇ one)).symm
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one)) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one))))) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (hole ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ ((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one))))) ◇ (one ◇ (one ◇ x))))))) (lemma_8 (one ◇ (one ◇ x)) ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one) one)
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one)) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one))) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ hole) ◇ (one ◇ (one ◇ x))))))) (lemma_13 ((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one)) (((one ◇ (one ◇ x)) ◇ one) ◇ one)).symm
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ one)) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (hole ◇ (one ◇ (one ◇ x))))))) (lemma_17 ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) (one ◇ (one ◇ x)) x)
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (((one ◇ (one ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ (hole ◇ (one ◇ (one ◇ x))))))) (lemma_13 (one ◇ (one ◇ x)) (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ hole)))) (lemma_14 (one ◇ (one ◇ x)) (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x))
    _ = (one ◇ (one ◇ ((((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ (hole ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x))))))) (axiom_3 one x ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)).symm
    _ = (one ◇ (one ◇ ((((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) ◇ ((one ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))) ◇ one)))) := congrArg (fun hole : G => (one ◇ (one ◇ ((((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) ◇ hole)))) (lemma_7 ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))).symm
    _ = (one ◇ (one ◇ ((((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) ◇ ((one ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))) ◇ (((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)))))) := congrArg (fun hole : G => (one ◇ (one ◇ hole))) (lemma_13 (((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) (one ◇ ((((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) ◇ (one ◇ (one ◇ x)))))
    _ = (one ◇ (one ◇ ((((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) ◇ one))) := congrArg (fun hole : G => (one ◇ (one ◇ ((((one ◇ x) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x)) ◇ hole)))) (lemma_22 (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ x) (one ◇ x) ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one))
    _ = (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one) ◇ one))) := congrArg (fun hole : G => (one ◇ (one ◇ (hole ◇ one)))) (axiom_3 one x ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ one))
    _ = (one ◇ (one ◇ ((((one ◇ x) ◇ one) ◇ one) ◇ one))) := congrArg (fun hole : G => (one ◇ (one ◇ (((hole ◇ one) ◇ one) ◇ one)))) (lemma_7 (one ◇ x))
    _ = (one ◇ (one ◇ ((x ◇ one) ◇ one))) := congrArg (fun hole : G => (one ◇ (one ◇ ((hole ◇ one) ◇ one)))) (lemma_7 x)
    _ = (one ◇ (x ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (lemma_4 (x ◇ one))
    _ = x := (lemma_4 x)

/-- info: 'CentralConstant.left_six' does not depend on any axioms -/
#guard_msgs in
#print axioms left_six

theorem left_square_hom (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (x y : G)  :
    ((one ◇ (one ◇ x)) ◇ (one ◇ (one ◇ y))) = (one ◇ (one ◇ (x ◇ y))) := by
  have dual (a b c : G) : ((c ◇ b) ◇ a) ◇ (a ◇ b) = a := by
    calc
      ((c ◇ b) ◇ a) ◇ (a ◇ b) =
          ((c ◇ b) ◇ a) ◇ (a ◇ ((c ◇ b) ◇ (b ◇ (c ◇ b)))) :=
        congrArg (fun t => ((c ◇ b) ◇ a) ◇ (a ◇ t)) (h b c b)
      _ = a := (h a (c ◇ b) (b ◇ (c ◇ b))).symm
  have axiom_1 (v_X : G) : (zero ◇ v_X) = one := by
    exact hzero v_X
  have axiom_2 (v_X v_Y v_Z : G) : ((v_X ◇ v_Y) ◇ (v_Y ◇ (v_X ◇ v_Z))) = v_Y := by
    exact (h v_Y v_X v_Z).symm
  have axiom_3 (v_X v_Y v_Z : G) : (((v_X ◇ v_Y) ◇ v_Z) ◇ (v_Z ◇ v_Y)) = v_Z := by
    exact dual v_Z v_Y v_X
  have lemma_4 (v_X : G) : (one ◇ (v_X ◇ one)) = v_X := by
    calc
      (one ◇ (v_X ◇ one)) = (one ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (one ◇ (v_X ◇ hole))) (axiom_1 zero).symm
      _ = ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (hole ◇ (v_X ◇ (zero ◇ zero)))) (axiom_1 v_X).symm
      _ = v_X := (axiom_2 zero v_X zero)
  have lemma_5 (v_X : G) : (v_X ◇ zero) = one := by
    calc
      (v_X ◇ zero) = (one ◇ ((v_X ◇ zero) ◇ one)) := (lemma_4 (v_X ◇ zero)).symm
      _ = (one ◇ ((v_X ◇ zero) ◇ (zero ◇ (v_X ◇ zero)))) := congrArg (fun hole : G => (one ◇ ((v_X ◇ zero) ◇ hole))) (axiom_1 (v_X ◇ zero)).symm
      _ = (one ◇ zero) := congrArg (fun hole : G => (one ◇ hole)) (axiom_2 v_X zero zero)
      _ = (one ◇ (one ◇ (zero ◇ one))) := congrArg (fun hole : G => (one ◇ hole)) (lemma_4 zero).symm
      _ = (one ◇ (one ◇ one)) := congrArg (fun hole : G => (one ◇ (one ◇ hole))) (axiom_1 one)
      _ = one := (lemma_4 one)
  have lemma_6 (v_W v_X v_Y v_Z : G) : (v_X ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W))) = (v_X ◇ (v_Y ◇ v_Z)) := by
    calc
      (v_X ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W))) = (((v_Y ◇ v_X) ◇ (v_X ◇ (v_Y ◇ v_Z))) ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W))) := congrArg (fun hole : G => (hole ◇ ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_X) ◇ v_W)))) (axiom_2 v_Y v_X v_Z).symm
      _ = (v_X ◇ (v_Y ◇ v_Z)) := (axiom_2 (v_Y ◇ v_X) (v_X ◇ (v_Y ◇ v_Z)) v_W)
  have lemma_7 (v_X : G) : ((one ◇ v_X) ◇ one) = v_X := by
    calc
      ((one ◇ v_X) ◇ one) = ((one ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((one ◇ v_X) ◇ hole)) (lemma_5 v_X).symm
      _ = (((zero ◇ zero) ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((hole ◇ v_X) ◇ (v_X ◇ zero))) (lemma_5 zero).symm
      _ = v_X := (axiom_3 zero zero v_X)
  have lemma_8 (v_X v_Y v_Z : G) : ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z)) = (v_X ◇ v_Y) := by
    calc
      ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z)) = ((one ◇ ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z))) ◇ one) := (lemma_7 ((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ v_Z))).symm
      _ = ((one ◇ (v_X ◇ v_Y)) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (lemma_6 v_Z one v_X v_Y)
      _ = (v_X ◇ v_Y) := (lemma_7 (v_X ◇ v_Y))
  have lemma_9 (v_W v_X v_Y v_Z : G) : (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ v_Y) = (v_Z ◇ v_Y) := by
    calc
      (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ v_Y) = (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ ((v_Z ◇ v_Y) ◇ (v_Y ◇ (v_Z ◇ v_W)))) := congrArg (fun hole : G => (((v_X ◇ (v_Y ◇ (v_Z ◇ v_W))) ◇ (v_Z ◇ v_Y)) ◇ hole)) (axiom_2 v_Z v_Y v_W).symm
      _ = (v_Z ◇ v_Y) := (axiom_3 v_X (v_Y ◇ (v_Z ◇ v_W)) (v_Z ◇ v_Y))
  have lemma_10 (v_X v_Y v_Z : G) : ((v_X ◇ (one ◇ (v_Y ◇ v_Z))) ◇ (v_Y ◇ one)) = v_Y := by
    calc
      ((v_X ◇ (one ◇ (v_Y ◇ v_Z))) ◇ (v_Y ◇ one)) = (one ◇ (((v_X ◇ (one ◇ (v_Y ◇ v_Z))) ◇ (v_Y ◇ one)) ◇ one)) := (lemma_4 ((v_X ◇ (one ◇ (v_Y ◇ v_Z))) ◇ (v_Y ◇ one))).symm
      _ = (one ◇ (v_Y ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (lemma_9 v_Z v_X one v_Y)
      _ = v_Y := (lemma_4 v_Y)
  have lemma_11 (v_X v_Y v_Z : G) : ((v_X ◇ (one ◇ v_Y)) ◇ ((v_Z ◇ v_Y) ◇ one)) = (v_Z ◇ v_Y) := by
    calc
      ((v_X ◇ (one ◇ v_Y)) ◇ ((v_Z ◇ v_Y) ◇ one)) = ((v_X ◇ (one ◇ ((v_Z ◇ v_Y) ◇ (v_Y ◇ (v_Z ◇ zero))))) ◇ ((v_Z ◇ v_Y) ◇ one)) := congrArg (fun hole : G => ((v_X ◇ (one ◇ hole)) ◇ ((v_Z ◇ v_Y) ◇ one))) (axiom_2 v_Z v_Y zero).symm
      _ = (v_Z ◇ v_Y) := (lemma_10 v_X (v_Z ◇ v_Y) (v_Y ◇ (v_Z ◇ zero)))
  have lemma_12 (v_X v_Y v_Z : G) : ((v_X ◇ v_Y) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one)) = (v_Z ◇ (v_Y ◇ one)) := by
    calc
      ((v_X ◇ v_Y) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one)) = ((v_X ◇ (one ◇ (v_Y ◇ one))) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one)) := congrArg (fun hole : G => ((v_X ◇ hole) ◇ ((v_Z ◇ (v_Y ◇ one)) ◇ one))) (lemma_4 v_Y).symm
      _ = (v_Z ◇ (v_Y ◇ one)) := (lemma_11 v_X (v_Y ◇ one) v_Z)
  have lemma_13 (v_X v_Y v_Z : G) : ((v_X ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ v_Z) ◇ one)) = (v_Y ◇ v_Z) := by
    calc
      ((v_X ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ v_Z) ◇ one)) = ((v_X ◇ (v_Y ◇ one)) ◇ (((one ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ one) ◇ one)) ◇ one)) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ one)) ◇ (hole ◇ one))) (lemma_8 v_Y v_Z one).symm
      _ = ((one ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ one) ◇ one)) := (lemma_12 v_X (v_Y ◇ one) (one ◇ (v_Y ◇ v_Z)))
      _ = (v_Y ◇ v_Z) := (lemma_8 v_Y v_Z one)
  have lemma_14 (v_X v_Y : G) : (v_X ◇ (v_Y ◇ one)) = (v_X ◇ (v_Y ◇ v_X)) := by
    calc
      (v_X ◇ (v_Y ◇ one)) = (v_X ◇ ((v_X ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ v_X) ◇ one))) := (lemma_6 one v_X v_Y one).symm
      _ = (v_X ◇ (v_Y ◇ v_X)) := congrArg (fun hole : G => (v_X ◇ hole)) (lemma_13 v_X v_Y v_X)
  have lemma_15 (v_X : G) : (v_X ◇ (one ◇ v_X)) = one := by
    calc
      (v_X ◇ (one ◇ v_X)) = (((one ◇ v_X) ◇ one) ◇ (one ◇ v_X)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_X))) (lemma_7 v_X).symm
      _ = one := (axiom_3 one v_X one)
  have lemma_16 (v_X v_Y : G) : ((v_X ◇ (v_Y ◇ v_X)) ◇ v_X) = (v_Y ◇ v_X) := by
    calc
      ((v_X ◇ (v_Y ◇ v_X)) ◇ v_X) = ((v_X ◇ (v_Y ◇ v_X)) ◇ ((v_Y ◇ v_X) ◇ (v_X ◇ (v_Y ◇ zero)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_X)) ◇ hole)) (axiom_2 v_Y v_X zero).symm
      _ = (v_Y ◇ v_X) := (axiom_2 v_X (v_Y ◇ v_X) (v_Y ◇ zero))
  have lemma_17 (v_X v_Y : G) : ((one ◇ v_X) ◇ v_Y) = ((v_Y ◇ v_X) ◇ v_Y) := by
    calc
      ((one ◇ v_X) ◇ v_Y) = ((v_Y ◇ ((one ◇ v_X) ◇ v_Y)) ◇ v_Y) := (lemma_16 v_Y (one ◇ v_X)).symm
      _ = ((v_Y ◇ ((one ◇ v_X) ◇ one)) ◇ v_Y) := congrArg (fun hole : G => (hole ◇ v_Y)) (lemma_14 v_Y (one ◇ v_X)).symm
      _ = ((v_Y ◇ v_X) ◇ v_Y) := congrArg (fun hole : G => ((v_Y ◇ hole) ◇ v_Y)) (lemma_7 v_X)
  have lemma_18 (v_X v_Y v_Z : G) : ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (v_X ◇ v_Z)) = ((one ◇ v_X) ◇ v_Y) := by
    calc
      ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (v_X ◇ v_Z)) = ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (((one ◇ v_X) ◇ one) ◇ v_Z)) := congrArg (fun hole : G => ((one ◇ ((one ◇ v_X) ◇ v_Y)) ◇ (hole ◇ v_Z))) (lemma_7 v_X).symm
      _ = ((one ◇ v_X) ◇ v_Y) := (lemma_8 (one ◇ v_X) v_Y v_Z)
  have lemma_19 (v_X v_Y v_Z : G) : (v_X ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ v_X)) = (v_Y ◇ ((v_X ◇ v_Z) ◇ one)) := by
    calc
      (v_X ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ v_X)) = (v_X ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ one)) := (lemma_14 v_X (v_Y ◇ ((v_X ◇ v_Z) ◇ one))).symm
      _ = ((((zero ◇ v_Z) ◇ v_X) ◇ (v_X ◇ v_Z)) ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ one)) := congrArg (fun hole : G => (hole ◇ ((v_Y ◇ ((v_X ◇ v_Z) ◇ one)) ◇ one))) (axiom_3 zero v_Z v_X).symm
      _ = (v_Y ◇ ((v_X ◇ v_Z) ◇ one)) := (lemma_12 ((zero ◇ v_Z) ◇ v_X) (v_X ◇ v_Z) v_Y)
  have lemma_20 (v_X v_Y v_Z : G) : (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ v_Y)) ◇ (v_X ◇ (v_Y ◇ one))) = (v_Z ◇ v_Y) := by
    calc
      (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ v_Y)) ◇ (v_X ◇ (v_Y ◇ one))) = (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ (one ◇ (v_Y ◇ one)))) ◇ (v_X ◇ (v_Y ◇ one))) := congrArg (fun hole : G => (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ hole)) ◇ (v_X ◇ (v_Y ◇ one)))) (lemma_4 v_Y).symm
      _ = (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ (one ◇ (v_Y ◇ one)))) ◇ ((v_Z ◇ (one ◇ (v_Y ◇ one))) ◇ ((v_X ◇ (v_Y ◇ one)) ◇ one))) := congrArg (fun hole : G => (((v_X ◇ (v_Y ◇ one)) ◇ (v_Z ◇ (one ◇ (v_Y ◇ one)))) ◇ hole)) (lemma_11 v_Z (v_Y ◇ one) v_X).symm
      _ = (v_Z ◇ (one ◇ (v_Y ◇ one))) := (axiom_2 (v_X ◇ (v_Y ◇ one)) (v_Z ◇ (one ◇ (v_Y ◇ one))) one)
      _ = (v_Z ◇ v_Y) := congrArg (fun hole : G => (v_Z ◇ hole)) (lemma_4 v_Y)
  have lemma_21 (v_X v_Y v_Z : G) : ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (v_X ◇ one))) = ((v_X ◇ (v_Y ◇ v_Z)) ◇ v_Z) := by
    calc
      ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (v_X ◇ one))) = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ hole))) (lemma_7 (v_X ◇ one)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_14 (one ◇ v_Z) (one ◇ (v_X ◇ one)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ hole))) (lemma_9 (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) one (one ◇ v_Z) (one ◇ (v_X ◇ one))).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (((one ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ (hole ◇ (one ◇ v_Z))))) (lemma_18 ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) one).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_19 (one ◇ v_Z) (one ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_18 ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) one)
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one)) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ hole) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_13 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z) ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z)
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ hole) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_14 (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one)))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ hole)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_14 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ hole))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_14 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ hole))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (axiom_2 (one ◇ (v_X ◇ one)) (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))) (v_Y ◇ v_Z)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))))) ◇ (((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ◇ hole)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_16 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ hole)) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (axiom_2 (one ◇ v_Z) ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))))) ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ v_Z) ◇ one))))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ hole))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_14 ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) (one ◇ v_Z)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ hole)))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_7 v_Z)
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((one ◇ hole) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))))) (lemma_14 (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) (one ◇ (v_X ◇ one))).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_17 ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one)) ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ hole))) (lemma_8 (one ◇ (v_X ◇ one)) (one ◇ v_Z) one).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one)))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((hole ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) ◇ ((one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ◇ (((one ◇ (v_X ◇ one)) ◇ one) ◇ one))))) (lemma_8 (one ◇ (v_X ◇ one)) (one ◇ v_Z) one).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ ((one ◇ (v_X ◇ one)) ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ hole)) (lemma_20 (one ◇ ((one ◇ (v_X ◇ one)) ◇ (one ◇ v_Z))) ((one ◇ (v_X ◇ one)) ◇ one) (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((v_X ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ hole))) (lemma_7 (v_X ◇ one))
      _ = (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((hole ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (lemma_4 v_X).symm
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => (hole ◇ ((((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (lemma_17 (v_X ◇ one) (v_Y ◇ v_Z))
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((hole ◇ v_Z) ◇ (v_X ◇ one)))) (lemma_17 (v_X ◇ one) (v_Y ◇ v_Z))
      _ = ((((v_Y ◇ v_Z) ◇ (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => (hole ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (axiom_3 v_Y v_Z (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))).symm
      _ = ((((((zero ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ ((v_Y ◇ v_Z) ◇ (v_X ◇ one))) ◇ (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => (((hole ◇ (((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z))) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (axiom_3 zero (v_X ◇ one) (v_Y ◇ v_Z)).symm
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one))) := congrArg (fun hole : G => ((hole ◇ ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z)) ◇ (((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) ◇ (v_X ◇ one)))) (axiom_3 (zero ◇ (v_X ◇ one)) (v_Y ◇ v_Z) ((v_Y ◇ v_Z) ◇ (v_X ◇ one)))
      _ = ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) := (axiom_3 (v_Y ◇ v_Z) (v_X ◇ one) ((((v_Y ◇ v_Z) ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z))
      _ = (((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ v_Z)) ◇ v_Z) := congrArg (fun hole : G => (hole ◇ v_Z)) (lemma_17 (v_X ◇ one) (v_Y ◇ v_Z)).symm
      _ = ((v_X ◇ (v_Y ◇ v_Z)) ◇ v_Z) := congrArg (fun hole : G => ((hole ◇ (v_Y ◇ v_Z)) ◇ v_Z)) (lemma_4 v_X)
  have lemma_22 (v_X v_Y v_Z : G) : ((one ◇ v_X) ◇ (v_Y ◇ (v_Z ◇ v_X))) = ((one ◇ v_X) ◇ (v_Y ◇ one)) := by
    calc
      ((one ◇ v_X) ◇ (v_Y ◇ (v_Z ◇ v_X))) = (((v_Y ◇ (v_Z ◇ v_X)) ◇ v_X) ◇ (v_Y ◇ (v_Z ◇ v_X))) := (lemma_17 v_X (v_Y ◇ (v_Z ◇ v_X)))
      _ = (((v_Y ◇ (v_Z ◇ v_X)) ◇ v_X) ◇ ((one ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ (v_Z ◇ v_X)) ◇ one))) := congrArg (fun hole : G => (((v_Y ◇ (v_Z ◇ v_X)) ◇ v_X) ◇ hole)) (lemma_13 one v_Y (v_Z ◇ v_X)).symm
      _ = (((v_Y ◇ (v_Z ◇ v_X)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ ((one ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ (v_Z ◇ v_X)) ◇ one))) := congrArg (fun hole : G => (hole ◇ ((one ◇ (v_Y ◇ one)) ◇ ((v_Y ◇ (v_Z ◇ v_X)) ◇ one)))) (lemma_21 v_Y v_Z v_X).symm
      _ = (((v_Y ◇ (v_Z ◇ v_X)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one)) := (lemma_21 (v_Y ◇ (v_Z ◇ v_X)) (one ◇ v_X) (v_Y ◇ one))
      _ = ((((one ◇ (v_Y ◇ (v_Z ◇ v_X))) ◇ ((v_Y ◇ one) ◇ one)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one)) := congrArg (fun hole : G => ((hole ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one))) (lemma_8 v_Y (v_Z ◇ v_X) one).symm
      _ = ((((one ◇ (v_Y ◇ (v_Z ◇ v_X))) ◇ ((v_Y ◇ one) ◇ ((one ◇ v_X) ◇ zero))) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one)) := congrArg (fun hole : G => ((((one ◇ (v_Y ◇ (v_Z ◇ v_X))) ◇ ((v_Y ◇ one) ◇ hole)) ◇ ((one ◇ v_X) ◇ (v_Y ◇ one))) ◇ (v_Y ◇ one))) (lemma_5 (one ◇ v_X)).symm
      _ = ((one ◇ v_X) ◇ (v_Y ◇ one)) := (lemma_9 zero (one ◇ (v_Y ◇ (v_Z ◇ v_X))) (v_Y ◇ one) (one ◇ v_X))
  have lemma_23 (v_X v_Y v_Z : G) : ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ v_X)) = one := by
    calc
      ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ v_X)) = ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (((zero ◇ (one ◇ v_Y)) ◇ v_X) ◇ (v_X ◇ (one ◇ v_Y))))) := congrArg (fun hole : G => ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ hole))) (axiom_3 zero (one ◇ v_Y) v_X).symm
      _ = ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) := (lemma_22 (v_X ◇ (one ◇ v_Y)) (v_Y ◇ v_Z) ((zero ◇ (one ◇ v_Y)) ◇ v_X))
      _ = ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y))))) := (lemma_22 (v_X ◇ (one ◇ v_Y)) (v_Y ◇ v_Z) one).symm
      _ = ((one ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ ((v_X ◇ (one ◇ v_Y)) ◇ ((one ◇ v_Y) ◇ (v_X ◇ zero)))) := (lemma_18 (v_X ◇ (one ◇ v_Y)) ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))) ((one ◇ v_Y) ◇ (v_X ◇ zero))).symm
      _ = ((one ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => ((one ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ hole)) (axiom_2 v_X (one ◇ v_Y) zero)
      _ = (((one ◇ v_Y) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y)))))) ◇ (one ◇ v_Y)) := (lemma_17 ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ (one ◇ (v_X ◇ (one ◇ v_Y))))) (one ◇ v_Y))
      _ = (((one ◇ v_Y) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (((one ◇ v_Y) ◇ hole) ◇ (one ◇ v_Y))) (lemma_14 (one ◇ (v_X ◇ (one ◇ v_Y))) (v_Y ◇ v_Z)).symm
      _ = (((((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) ◇ v_Y) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (lemma_17 v_Y ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)))
      _ = (((((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) ◇ (((zero ◇ v_Z) ◇ v_Y) ◇ (v_Y ◇ v_Z))) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (((((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one)) ◇ hole) ◇ ((one ◇ (v_X ◇ (one ◇ v_Y))) ◇ ((v_Y ◇ v_Z) ◇ one))) ◇ (one ◇ v_Y))) (axiom_3 zero v_Z v_Y).symm
      _ = ((((zero ◇ v_Z) ◇ v_Y) ◇ (v_Y ◇ v_Z)) ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (lemma_20 (one ◇ (v_X ◇ (one ◇ v_Y))) (v_Y ◇ v_Z) ((zero ◇ v_Z) ◇ v_Y))
      _ = (v_Y ◇ (one ◇ v_Y)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_Y))) (axiom_3 zero v_Z v_Y)
      _ = one := (lemma_15 v_Y)
  have lemma_24 (v_X v_Y v_Z : G) : ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z)) = v_X := by
    calc
      ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z)) = ((one ◇ ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))) ◇ one) := (lemma_7 ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))).symm
      _ = (((((v_Y ◇ v_X) ◇ one) ◇ (one ◇ v_X)) ◇ ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))) ◇ one) := congrArg (fun hole : G => ((hole ◇ ((one ◇ v_X) ◇ (((v_Y ◇ v_X) ◇ one) ◇ v_Z))) ◇ one)) (axiom_3 v_Y v_X one).symm
      _ = ((one ◇ v_X) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (axiom_2 ((v_Y ◇ v_X) ◇ one) (one ◇ v_X) v_Z)
      _ = v_X := (lemma_7 v_X)
  have lemma_25 (v_X v_Y v_Z : G) : (((v_X ◇ v_Y) ◇ (v_Z ◇ (v_X ◇ v_Z))) ◇ (v_X ◇ one)) = (v_Z ◇ (v_X ◇ v_Z)) := by
    calc
      (((v_X ◇ v_Y) ◇ (v_Z ◇ (v_X ◇ v_Z))) ◇ (v_X ◇ one)) = (((v_X ◇ v_Y) ◇ (v_Z ◇ (v_X ◇ one))) ◇ (v_X ◇ one)) := congrArg (fun hole : G => (((v_X ◇ v_Y) ◇ hole) ◇ (v_X ◇ one))) (lemma_14 v_Z v_X).symm
      _ = ((((one ◇ (v_X ◇ v_Y)) ◇ ((v_X ◇ one) ◇ (v_Z ◇ zero))) ◇ (v_Z ◇ (v_X ◇ one))) ◇ (v_X ◇ one)) := congrArg (fun hole : G => ((hole ◇ (v_Z ◇ (v_X ◇ one))) ◇ (v_X ◇ one))) (lemma_8 v_X v_Y (v_Z ◇ zero)).symm
      _ = (v_Z ◇ (v_X ◇ one)) := (lemma_9 zero (one ◇ (v_X ◇ v_Y)) (v_X ◇ one) v_Z)
      _ = (v_Z ◇ (v_X ◇ v_Z)) := (lemma_14 v_Z v_X)
  have lemma_26 (v_X v_Y v_Z : G) : (v_X ◇ (v_Y ◇ (v_Z ◇ (v_X ◇ v_Z)))) = (v_X ◇ (v_Y ◇ v_X)) := by
    calc
      (v_X ◇ (v_Y ◇ (v_Z ◇ (v_X ◇ v_Z)))) = ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ (v_Z ◇ (v_X ◇ v_Z)))) := congrArg (fun hole : G => (hole ◇ (v_Y ◇ (v_Z ◇ (v_X ◇ v_Z))))) (lemma_4 v_X).symm
      _ = ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ (((v_X ◇ zero) ◇ (v_Z ◇ (v_X ◇ v_Z))) ◇ (v_X ◇ one)))) := congrArg (fun hole : G => ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ hole))) (lemma_25 v_X zero v_Z).symm
      _ = ((one ◇ (v_X ◇ one)) ◇ (v_Y ◇ one)) := (lemma_22 (v_X ◇ one) v_Y ((v_X ◇ zero) ◇ (v_Z ◇ (v_X ◇ v_Z))))
      _ = (v_X ◇ (v_Y ◇ one)) := congrArg (fun hole : G => (hole ◇ (v_Y ◇ one))) (lemma_4 v_X)
      _ = (v_X ◇ (v_Y ◇ v_X)) := (lemma_14 v_X v_Y)
  have lemma_27 (v_X v_Y v_Z : G) : ((v_X ◇ one) ◇ (v_Y ◇ (v_X ◇ v_Z))) = ((v_X ◇ one) ◇ (v_Y ◇ one)) := by
    calc
      ((v_X ◇ one) ◇ (v_Y ◇ (v_X ◇ v_Z))) = ((v_X ◇ one) ◇ (v_Y ◇ ((one ◇ (v_X ◇ v_Z)) ◇ ((v_X ◇ one) ◇ (one ◇ (v_X ◇ v_Z)))))) := congrArg (fun hole : G => ((v_X ◇ one) ◇ (v_Y ◇ hole))) (lemma_8 v_X v_Z (one ◇ (v_X ◇ v_Z))).symm
      _ = ((v_X ◇ one) ◇ (v_Y ◇ (v_X ◇ one))) := (lemma_26 (v_X ◇ one) v_Y (one ◇ (v_X ◇ v_Z)))
      _ = ((v_X ◇ one) ◇ (v_Y ◇ one)) := (lemma_14 (v_X ◇ one) v_Y).symm
  have lemma_28 (v_X v_Y v_Z : G) : ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X)) = (v_Z ◇ (one ◇ v_X)) := by
    calc
      ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X)) = ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ ((((one ◇ v_Z) ◇ ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X))) ◇ (one ◇ v_X)) ◇ ((one ◇ v_X) ◇ ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X))))) := congrArg (fun hole : G => ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ hole)) (axiom_3 (one ◇ v_Z) ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X)) (one ◇ v_X)).symm
      _ = ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ ((v_Z ◇ (one ◇ v_X)) ◇ ((one ◇ v_X) ◇ ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X))))) := congrArg (fun hole : G => ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ ((hole ◇ (one ◇ v_X)) ◇ ((one ◇ v_X) ◇ ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ (one ◇ v_X)))))) (lemma_24 v_Z (v_X ◇ v_Y) (one ◇ v_X))
      _ = ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ ((v_Z ◇ (one ◇ v_X)) ◇ (((v_X ◇ v_Y) ◇ v_Z) ◇ one))) := (lemma_26 (((v_X ◇ v_Y) ◇ v_Z) ◇ one) (v_Z ◇ (one ◇ v_X)) (one ◇ v_X))
      _ = ((((v_X ◇ v_Y) ◇ v_Z) ◇ one) ◇ ((v_Z ◇ (one ◇ v_X)) ◇ one)) := (lemma_27 ((v_X ◇ v_Y) ◇ v_Z) (v_Z ◇ (one ◇ v_X)) one)
      _ = ((((v_X ◇ v_Y) ◇ v_Z) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ ((v_X ◇ v_Y) ◇ v_Z))) ◇ ((v_Z ◇ (one ◇ v_X)) ◇ one)) := congrArg (fun hole : G => ((((v_X ◇ v_Y) ◇ v_Z) ◇ hole) ◇ ((v_Z ◇ (one ◇ v_X)) ◇ one))) (lemma_23 v_Z v_X v_Y).symm
      _ = (((((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ zero) ◇ (((v_X ◇ v_Y) ◇ v_Z) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ ((v_X ◇ v_Y) ◇ v_Z)))) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ one)) ◇ ((v_Z ◇ (one ◇ v_X)) ◇ one)) := congrArg (fun hole : G => (hole ◇ ((v_Z ◇ (one ◇ v_X)) ◇ one))) (lemma_25 (one ◇ (v_Z ◇ (one ◇ v_X))) zero ((v_X ◇ v_Y) ◇ v_Z)).symm
      _ = (((((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ zero) ◇ (((v_X ◇ v_Y) ◇ v_Z) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ ((v_X ◇ v_Y) ◇ v_Z)))) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ one)) ◇ (((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ (((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ one) ◇ one)) ◇ one)) := congrArg (fun hole : G => (((((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ zero) ◇ (((v_X ◇ v_Y) ◇ v_Z) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ ((v_X ◇ v_Y) ◇ v_Z)))) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ one)) ◇ (hole ◇ one))) (lemma_24 (v_Z ◇ (one ◇ v_X)) one one).symm
      _ = ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ (((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ one) ◇ one)) := (lemma_12 (((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ zero) ◇ (((v_X ◇ v_Y) ◇ v_Z) ◇ ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ ((v_X ◇ v_Y) ◇ v_Z)))) ((one ◇ (v_Z ◇ (one ◇ v_X))) ◇ one) (one ◇ (v_Z ◇ (one ◇ v_X))))
      _ = (v_Z ◇ (one ◇ v_X)) := (lemma_24 (v_Z ◇ (one ◇ v_X)) one one)
  have lemma_29 (v_X v_Y : G) : (((v_X ◇ v_Y) ◇ one) ◇ one) = (v_Y ◇ (one ◇ (one ◇ v_X))) := by
    calc
      (((v_X ◇ v_Y) ◇ one) ◇ one) = (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ v_Y) ◇ one) ◇ one) := congrArg (fun hole : G => (((hole ◇ v_Y) ◇ one) ◇ one)) (axiom_2 zero v_X zero).symm
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ one) := congrArg (fun hole : G => (((hole ◇ v_Y) ◇ one) ◇ one)) (lemma_7 ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))).symm
      _ = (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (axiom_3 (zero ◇ v_X) (v_X ◇ (zero ◇ zero)) ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)).symm
      _ = (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((one ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) ◇ ((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) ◇ hole)) (lemma_23 (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)).symm
      _ = (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((one ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) ◇ one)) := (lemma_14 ((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) (one ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))).symm
      _ = (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one)) ◇ (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))) ◇ hole)) (lemma_7 ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (hole ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (axiom_3 (zero ◇ v_X) (v_X ◇ (zero ◇ zero)) ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one))
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ hole)) (lemma_16 (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))).symm
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one)) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (hole ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (lemma_14 (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero)))).symm
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one)) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (hole ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (lemma_19 ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) (v_X ◇ (zero ◇ zero))).symm
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one)) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ ((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one))))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ hole) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (lemma_14 ((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one)) (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y))
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (((one ◇ ((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one))) ◇ (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y)) ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ ((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one))))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (hole ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ ((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one))))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (lemma_8 (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one) v_Y).symm
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y)) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ hole) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (axiom_3 one ((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (v_X ◇ (zero ◇ zero))) ◇ one)) (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y))
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (one ◇ ((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one))) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ ((((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ hole) ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (lemma_4 (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y)).symm
      _ = (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (one ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := congrArg (fun hole : G => (((((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) ◇ one) ◇ (hole ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))))))) (axiom_2 (((one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) ◇ one) ◇ v_Y) one one)
      _ = (v_Y ◇ (one ◇ (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))))) := (lemma_28 (one ◇ ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero)))) one v_Y)
      _ = (v_Y ◇ (one ◇ (one ◇ v_X))) := congrArg (fun hole : G => (v_Y ◇ (one ◇ (one ◇ hole)))) (axiom_2 zero v_X zero)
  have lemma_30 (v_X v_Y : G) : (one ◇ (v_X ◇ (one ◇ (one ◇ v_Y)))) = ((v_Y ◇ v_X) ◇ one) := by
    calc
      (one ◇ (v_X ◇ (one ◇ (one ◇ v_Y)))) = (one ◇ (((v_Y ◇ v_X) ◇ one) ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (lemma_29 v_Y v_X).symm
      _ = ((v_Y ◇ v_X) ◇ one) := (lemma_4 ((v_Y ◇ v_X) ◇ one))
  have lemma_31 (v_X v_Y v_Z : G) : ((v_X ◇ ((v_Y ◇ one) ◇ v_Z)) ◇ v_Y) = ((v_X ◇ one) ◇ v_Y) := by
    calc
      ((v_X ◇ ((v_Y ◇ one) ◇ v_Z)) ◇ v_Y) = ((v_X ◇ ((v_Y ◇ one) ◇ v_Z)) ◇ (one ◇ (v_Y ◇ one))) := congrArg (fun hole : G => ((v_X ◇ ((v_Y ◇ one) ◇ v_Z)) ◇ hole)) (lemma_4 v_Y).symm
      _ = (((((v_Y ◇ one) ◇ v_X) ◇ (v_X ◇ ((v_Y ◇ one) ◇ v_Z))) ◇ one) ◇ (one ◇ (v_Y ◇ one))) := (lemma_28 (v_Y ◇ one) v_X (v_X ◇ ((v_Y ◇ one) ◇ v_Z))).symm
      _ = ((v_X ◇ one) ◇ (one ◇ (v_Y ◇ one))) := congrArg (fun hole : G => ((hole ◇ one) ◇ (one ◇ (v_Y ◇ one)))) (axiom_2 (v_Y ◇ one) v_X v_Z)
      _ = ((v_X ◇ one) ◇ v_Y) := congrArg (fun hole : G => ((v_X ◇ one) ◇ hole)) (lemma_4 v_Y)
  calc
    ((one ◇ (one ◇ x)) ◇ (one ◇ (one ◇ y))) = (((y ◇ (one ◇ (one ◇ x))) ◇ one) ◇ one) := (lemma_29 y (one ◇ (one ◇ x))).symm
    _ = (((y ◇ (one ◇ (one ◇ x))) ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) := congrArg (fun hole : G => (((y ◇ (one ◇ (one ◇ x))) ◇ one) ◇ hole)) (lemma_15 (one ◇ (y ◇ (one ◇ (one ◇ x))))).symm
    _ = (((((zero ◇ ((zero ◇ (one ◇ x)) ◇ one)) ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ ((y ◇ (one ◇ (one ◇ x))) ◇ ((zero ◇ (one ◇ x)) ◇ one))) ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) := congrArg (fun hole : G => ((hole ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x)))))))) (axiom_3 zero ((zero ◇ (one ◇ x)) ◇ one) (y ◇ (one ◇ (one ◇ x)))).symm
    _ = ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ ((y ◇ (one ◇ (one ◇ x))) ◇ ((zero ◇ (one ◇ x)) ◇ one))) ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) := congrArg (fun hole : G => ((((hole ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ ((y ◇ (one ◇ (one ◇ x))) ◇ ((zero ◇ (one ◇ x)) ◇ one))) ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x)))))))) (axiom_1 ((zero ◇ (one ◇ x)) ◇ one))
    _ = ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) := congrArg (fun hole : G => ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ hole) ◇ one) ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x)))))))) (lemma_11 y (one ◇ x) zero)
    _ = ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ one) ◇ ((one ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) ◇ one)) := congrArg (fun hole : G => ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ one) ◇ hole)) (lemma_7 ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))).symm
    _ = ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ one) ◇ ((one ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) ◇ (((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) := (lemma_27 ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) (one ◇ ((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) (one ◇ (y ◇ (one ◇ (one ◇ x))))).symm
    _ = ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ one) ◇ one) := congrArg (fun hole : G => ((((one ◇ (y ◇ (one ◇ (one ◇ x)))) ◇ (zero ◇ (one ◇ x))) ◇ one) ◇ hole)) (lemma_23 (one ◇ (y ◇ (one ◇ (one ◇ x)))) (one ◇ (y ◇ (one ◇ (one ◇ x)))) (zero ◇ (one ◇ x)))
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ x))))))) := (lemma_29 (one ◇ (y ◇ (one ◇ (one ◇ x)))) (zero ◇ (one ◇ x)))
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ (one ◇ (y ◇ (one ◇ ((one ◇ (one ◇ x)) ◇ one))))))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ (one ◇ (y ◇ hole)))))) (lemma_4 (one ◇ (one ◇ x))).symm
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ (one ◇ (y ◇ (one ◇ (one ◇ (((one ◇ (one ◇ x)) ◇ one) ◇ one)))))))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ (one ◇ (y ◇ (one ◇ hole))))))) (lemma_4 ((one ◇ (one ◇ x)) ◇ one)).symm
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ y) ◇ one)))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (one ◇ hole)))) (lemma_30 y (((one ◇ (one ◇ x)) ◇ one) ◇ one))
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (((one ◇ one) ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ y)) ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ y) ◇ one)))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (hole ◇ (((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ y) ◇ one))))) (lemma_24 one (one ◇ (one ◇ x)) y).symm
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ hole))) (axiom_3 one one ((((one ◇ (one ◇ x)) ◇ one) ◇ one) ◇ y))
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ ((one ◇ (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x)))))) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (hole ◇ y)))) (lemma_30 one (one ◇ (one ◇ x))).symm
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ ((y ◇ (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x)))))) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ hole))) (lemma_17 (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) y)
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ ((y ◇ (((one ◇ x) ◇ one) ◇ one)) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ ((y ◇ hole) ◇ y)))) (lemma_30 one (one ◇ x))
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (((one ◇ x) ◇ ((y ◇ (((one ◇ x) ◇ one) ◇ one)) ◇ (one ◇ x))) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (hole ◇ y)))) (lemma_19 (one ◇ x) y one).symm
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (((one ◇ x) ◇ ((y ◇ one) ◇ (one ◇ x))) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (((one ◇ x) ◇ hole) ◇ y)))) (lemma_31 y (one ◇ x) one)
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (((one ◇ x) ◇ ((y ◇ one) ◇ one)) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ (hole ◇ y)))) (lemma_14 (one ◇ x) (y ◇ one)).symm
    _ = ((zero ◇ (one ◇ x)) ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ x)) ◇ (one ◇ hole))) (lemma_31 (one ◇ x) y one)
    _ = ((zero ◇ (one ◇ ((one ◇ x) ◇ one))) ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) := congrArg (fun hole : G => ((zero ◇ hole) ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y)))) (lemma_4 (one ◇ x)).symm
    _ = ((zero ◇ (one ◇ ((one ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) ◇ (((one ◇ x) ◇ one) ◇ one)))) ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) := congrArg (fun hole : G => ((zero ◇ (one ◇ hole)) ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y)))) (lemma_10 one ((one ◇ x) ◇ one) y).symm
    _ = ((zero ◇ (one ◇ ((one ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) ◇ (((one ◇ x) ◇ one) ◇ one)))) ◇ ((one ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) ◇ one)) := congrArg (fun hole : G => ((zero ◇ (one ◇ ((one ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) ◇ (((one ◇ x) ◇ one) ◇ one)))) ◇ hole)) (lemma_7 (one ◇ (((one ◇ x) ◇ one) ◇ y))).symm
    _ = (one ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) := (lemma_10 zero (one ◇ (one ◇ (((one ◇ x) ◇ one) ◇ y))) (((one ◇ x) ◇ one) ◇ one))
    _ = (one ◇ (one ◇ (x ◇ y))) := congrArg (fun hole : G => (one ◇ (one ◇ (hole ◇ y)))) (lemma_7 x)

/-- info: 'CentralConstant.left_square_hom' does not depend on any axioms -/
#guard_msgs in
#print axioms left_square_hom

theorem left_cube_fixed (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (x : G) (hfixed : one ◇ (one ◇ (one ◇ x)) = x) :
    zero = one := by
  have dual (a b c : G) : ((c ◇ b) ◇ a) ◇ (a ◇ b) = a := by
    calc
      ((c ◇ b) ◇ a) ◇ (a ◇ b) =
          ((c ◇ b) ◇ a) ◇ (a ◇ ((c ◇ b) ◇ (b ◇ (c ◇ b)))) :=
        congrArg (fun t => ((c ◇ b) ◇ a) ◇ (a ◇ t)) (h b c b)
      _ = a := (h a (c ◇ b) (b ◇ (c ◇ b))).symm
  have axiom_1 (v_X : G) : (zero ◇ v_X) = one := by
    exact hzero v_X
  have axiom_2 : (one ◇ (one ◇ (one ◇ x))) = x := by
    exact hfixed
  have axiom_3 (v_X v_Y v_Z : G) : ((v_X ◇ v_Y) ◇ (v_Y ◇ (v_X ◇ v_Z))) = v_Y := by
    exact (h v_Y v_X v_Z).symm
  have axiom_4 (v_X v_Y v_Z : G) : (((v_X ◇ v_Y) ◇ v_Z) ◇ (v_Z ◇ v_Y)) = v_Z := by
    exact dual v_Z v_Y v_X
  have lemma_5 (v_X : G) : (one ◇ (v_X ◇ one)) = v_X := by
    calc
      (one ◇ (v_X ◇ one)) = (one ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (one ◇ (v_X ◇ hole))) (axiom_1 zero).symm
      _ = ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (hole ◇ (v_X ◇ (zero ◇ zero)))) (axiom_1 v_X).symm
      _ = v_X := (axiom_3 zero v_X zero)
  have lemma_6 : (one ◇ one) = zero := by
    calc
      (one ◇ one) = (one ◇ (zero ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (axiom_1 one).symm
      _ = zero := (lemma_5 zero)
  have lemma_7 (v_X : G) : (v_X ◇ zero) = one := by
    calc
      (v_X ◇ zero) = (one ◇ ((v_X ◇ zero) ◇ one)) := (lemma_5 (v_X ◇ zero)).symm
      _ = (one ◇ ((v_X ◇ zero) ◇ (zero ◇ (v_X ◇ zero)))) := congrArg (fun hole : G => (one ◇ ((v_X ◇ zero) ◇ hole))) (axiom_1 (v_X ◇ zero)).symm
      _ = (one ◇ zero) := congrArg (fun hole : G => (one ◇ hole)) (axiom_3 v_X zero zero)
      _ = (one ◇ (one ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (lemma_6).symm
      _ = one := (lemma_5 one)
  have lemma_8 (v_X : G) : ((one ◇ v_X) ◇ one) = v_X := by
    calc
      ((one ◇ v_X) ◇ one) = ((one ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((one ◇ v_X) ◇ hole)) (lemma_7 v_X).symm
      _ = (((zero ◇ zero) ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((hole ◇ v_X) ◇ (v_X ◇ zero))) (lemma_7 zero).symm
      _ = v_X := (axiom_4 zero zero v_X)
  have lemma_9 (v_X : G) : (v_X ◇ (one ◇ v_X)) = one := by
    calc
      (v_X ◇ (one ◇ v_X)) = (((one ◇ v_X) ◇ one) ◇ (one ◇ v_X)) := congrArg (fun hole : G => (hole ◇ (one ◇ v_X))) (lemma_8 v_X).symm
      _ = one := (axiom_4 one v_X one)
  have lemma_10 : (one ◇ (one ◇ x)) = (x ◇ one) := by
    calc
      (one ◇ (one ◇ x)) = ((one ◇ (one ◇ (one ◇ x))) ◇ one) := (lemma_8 (one ◇ (one ◇ x))).symm
      _ = (x ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (axiom_2)
  have lemma_11 (v_X v_Y : G) : ((one ◇ v_X) ◇ (v_X ◇ v_Y)) = v_X := by
    calc
      ((one ◇ v_X) ◇ (v_X ◇ v_Y)) = (((zero ◇ v_Y) ◇ v_X) ◇ (v_X ◇ v_Y)) := congrArg (fun hole : G => ((hole ◇ v_X) ◇ (v_X ◇ v_Y))) (axiom_1 v_Y).symm
      _ = v_X := (axiom_4 zero v_Y v_X)
  calc
    zero = (one ◇ one) := (lemma_6).symm
    _ = (((one ◇ x) ◇ (one ◇ (one ◇ x))) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (lemma_9 (one ◇ x)).symm
    _ = (((one ◇ x) ◇ (x ◇ one)) ◇ one) := congrArg (fun hole : G => (((one ◇ x) ◇ hole) ◇ one)) (lemma_10)
    _ = (x ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (lemma_11 x one)
    _ = (one ◇ (one ◇ x)) := (lemma_10).symm
    _ = (((one ◇ x) ◇ (one ◇ (one ◇ x))) ◇ ((one ◇ (one ◇ x)) ◇ ((one ◇ x) ◇ (one ◇ zero)))) := (axiom_3 (one ◇ x) (one ◇ (one ◇ x)) (one ◇ zero)).symm
    _ = (((one ◇ x) ◇ (one ◇ (one ◇ x))) ◇ (one ◇ x)) := congrArg (fun hole : G => (((one ◇ x) ◇ (one ◇ (one ◇ x))) ◇ hole)) (axiom_3 one (one ◇ x) zero)
    _ = (((one ◇ x) ◇ (x ◇ one)) ◇ (one ◇ x)) := congrArg (fun hole : G => (((one ◇ x) ◇ hole) ◇ (one ◇ x))) (lemma_10)
    _ = (x ◇ (one ◇ x)) := congrArg (fun hole : G => (hole ◇ (one ◇ x))) (lemma_11 x one)
    _ = one := (lemma_9 x)

/-- info: 'CentralConstant.left_cube_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms left_cube_fixed

theorem idempotent_left_square_fixed (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (x : G) (hidem : x ◇ x = x) (hfixed : one ◇ (one ◇ x) = x) :
    zero = one := by
  have dual (a b c : G) : ((c ◇ b) ◇ a) ◇ (a ◇ b) = a := by
    calc
      ((c ◇ b) ◇ a) ◇ (a ◇ b) =
          ((c ◇ b) ◇ a) ◇ (a ◇ ((c ◇ b) ◇ (b ◇ (c ◇ b)))) :=
        congrArg (fun t => ((c ◇ b) ◇ a) ◇ (a ◇ t)) (h b c b)
      _ = a := (h a (c ◇ b) (b ◇ (c ◇ b))).symm
  have axiom_1 (v_X : G) : (zero ◇ v_X) = one := by
    exact hzero v_X
  have axiom_2 : (x ◇ x) = x := by
    exact hidem
  have axiom_3 : (one ◇ (one ◇ x)) = x := by
    exact hfixed
  have axiom_4 (v_X v_Y v_Z : G) : ((v_X ◇ v_Y) ◇ (v_Y ◇ (v_X ◇ v_Z))) = v_Y := by
    exact (h v_Y v_X v_Z).symm
  have axiom_5 (v_X v_Y v_Z : G) : (((v_X ◇ v_Y) ◇ v_Z) ◇ (v_Z ◇ v_Y)) = v_Z := by
    exact dual v_Z v_Y v_X
  have lemma_6 (v_X v_Y : G) : ((one ◇ v_X) ◇ (v_X ◇ v_Y)) = v_X := by
    calc
      ((one ◇ v_X) ◇ (v_X ◇ v_Y)) = (((zero ◇ v_Y) ◇ v_X) ◇ (v_X ◇ v_Y)) := congrArg (fun hole : G => ((hole ◇ v_X) ◇ (v_X ◇ v_Y))) (axiom_1 v_Y).symm
      _ = v_X := (axiom_5 zero v_Y v_X)
  have lemma_7 : (one ◇ x) = x := by
    calc
      (one ◇ x) = ((one ◇ (one ◇ x)) ◇ ((one ◇ x) ◇ x)) := (lemma_6 (one ◇ x) x).symm
      _ = ((one ◇ (one ◇ x)) ◇ ((one ◇ x) ◇ (x ◇ x))) := congrArg (fun hole : G => ((one ◇ (one ◇ x)) ◇ ((one ◇ x) ◇ hole))) (axiom_2).symm
      _ = ((one ◇ (one ◇ x)) ◇ x) := congrArg (fun hole : G => ((one ◇ (one ◇ x)) ◇ hole)) (lemma_6 x x)
      _ = (x ◇ x) := congrArg (fun hole : G => (hole ◇ x)) (axiom_3)
      _ = x := (axiom_2)
  have lemma_8 (v_X : G) : (one ◇ (v_X ◇ one)) = v_X := by
    calc
      (one ◇ (v_X ◇ one)) = (one ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (one ◇ (v_X ◇ hole))) (axiom_1 zero).symm
      _ = ((zero ◇ v_X) ◇ (v_X ◇ (zero ◇ zero))) := congrArg (fun hole : G => (hole ◇ (v_X ◇ (zero ◇ zero)))) (axiom_1 v_X).symm
      _ = v_X := (axiom_4 zero v_X zero)
  have lemma_9 : (one ◇ one) = zero := by
    calc
      (one ◇ one) = (one ◇ (zero ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (axiom_1 one).symm
      _ = zero := (lemma_8 zero)
  have lemma_10 (v_X : G) : (v_X ◇ zero) = one := by
    calc
      (v_X ◇ zero) = (one ◇ ((v_X ◇ zero) ◇ one)) := (lemma_8 (v_X ◇ zero)).symm
      _ = (one ◇ ((v_X ◇ zero) ◇ (zero ◇ (v_X ◇ zero)))) := congrArg (fun hole : G => (one ◇ ((v_X ◇ zero) ◇ hole))) (axiom_1 (v_X ◇ zero)).symm
      _ = (one ◇ zero) := congrArg (fun hole : G => (one ◇ hole)) (axiom_4 v_X zero zero)
      _ = (one ◇ (one ◇ one)) := congrArg (fun hole : G => (one ◇ hole)) (lemma_9).symm
      _ = one := (lemma_8 one)
  have lemma_11 (v_X : G) : ((one ◇ v_X) ◇ one) = v_X := by
    calc
      ((one ◇ v_X) ◇ one) = ((one ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((one ◇ v_X) ◇ hole)) (lemma_10 v_X).symm
      _ = (((zero ◇ zero) ◇ v_X) ◇ (v_X ◇ zero)) := congrArg (fun hole : G => ((hole ◇ v_X) ◇ (v_X ◇ zero))) (lemma_10 zero).symm
      _ = v_X := (axiom_5 zero zero v_X)
  have lemma_12 : x = one := by
    calc
      x = (x ◇ x) := (axiom_2).symm
      _ = (x ◇ (one ◇ x)) := congrArg (fun hole : G => (x ◇ hole)) (lemma_7).symm
      _ = (((one ◇ x) ◇ one) ◇ (one ◇ x)) := congrArg (fun hole : G => (hole ◇ (one ◇ x))) (lemma_11 x).symm
      _ = one := (axiom_5 one x one)
  calc
    zero = (one ◇ one) := (lemma_9).symm
    _ = (x ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (lemma_12).symm
    _ = ((one ◇ (one ◇ x)) ◇ one) := congrArg (fun hole : G => (hole ◇ one)) (axiom_3).symm
    _ = (one ◇ x) := (lemma_11 (one ◇ x))
    _ = x := (lemma_7)
    _ = one := (lemma_12)

/-- info: 'CentralConstant.idempotent_left_square_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms idempotent_left_square_fixed

/- END REPLAYED PROOFS -/
private theorem prime_dvd_card_of_fixedPointFree {A : Type*} [Finite A]
    (p : ℕ) [Fact p.Prime] (f : Function.End A) (hf : f ^ p = 1)
    (hfree : ∀ x, f x ≠ x) : p ∣ Nat.card A := by
  classical
  letI := Fintype.ofFinite A
  letI : IsEmpty f.fixedPoints := ⟨fun x => hfree x.val x.property⟩
  have hm := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) (f := f)
    (by simpa only [pow_one] using hf)
  have he : Fintype.card f.fixedPoints = 0 := Fintype.card_eq_zero
  rw [he] at hm
  simpa only [Nat.card_eq_fintype_card] using Nat.modEq_zero_iff_dvd.mp hm

theorem even_card_of_constant_row [Finite G] (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (hne : zero ≠ one) : 2 ∣ Nat.card G := by
  let f : Function.End G := fun x => one ◇ (one ◇ (one ◇ x))
  apply prime_dvd_card_of_fixedPointFree 2 f
  · funext x
    change one ◇ (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x))))) = x
    exact left_six h zero one hzero x
  · intro x hx
    exact hne (left_cube_fixed h zero one hzero x hx)

theorem three_dvd_idempotents [Finite G] (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (hne : zero ≠ one) :
    3 ∣ Nat.card {x : G // x ◇ x = x} := by
  let f : Function.End {x : G // x ◇ x = x} := fun x =>
    ⟨one ◇ (one ◇ x.val), by
      rw [left_square_hom h zero one hzero x.val x.val, x.property]⟩
  apply prime_dvd_card_of_fixedPointFree 3 f
  · funext x
    apply Subtype.ext
    change one ◇ (one ◇ (one ◇ (one ◇ (one ◇ (one ◇ x.val))))) = x.val
    exact left_six h zero one hzero x.val
  · intro x hx
    have he : one ◇ (one ◇ x.val) = x.val := congrArg Subtype.val hx
    exact hne (idempotent_left_square_fixed h zero one hzero x.val x.property he)

theorem constant_values_ne [Nontrivial G] (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) : zero ≠ one := by
  intro heq
  have hall (x : G) : x = zero := by simpa only [hzero, ← heq] using h x zero zero
  obtain ⟨x, hx⟩ := exists_ne zero
  exact hx (hall x)

theorem five_idempotents_no_constant_row [Finite G] [Nontrivial G]
    (h : Equation1483 G) (hcard : Nat.card {x : G // x ◇ x = x} = 5) :
    ¬ ∃ zero one : G, ∀ t : G, zero ◇ t = one := by
  rintro ⟨zero, one, hzero⟩
  have hd := three_dvd_idempotents h zero one hzero (constant_values_ne h zero one hzero)
  rw [hcard] at hd
  exact (by decide : ¬ 3 ∣ 5) hd

/-- info: 'CentralConstant.even_card_of_constant_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms even_card_of_constant_row
/-- info: 'CentralConstant.three_dvd_idempotents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_dvd_idempotents
/-- info: 'CentralConstant.five_idempotents_no_constant_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms five_idempotents_no_constant_row

theorem bijective_row_gives_constant (h : Equation1483 G) (a : G)
    (ha : Function.Bijective (fun x => a ◇ x)) : ∃ b c : G, ∀ z, b ◇ z = c := by
  have dual (x y z : G) : ((z ◇ y) ◇ x) ◇ (x ◇ y) = x := by
    calc
      ((z ◇ y) ◇ x) ◇ (x ◇ y) =
          ((z ◇ y) ◇ x) ◇ (x ◇ ((z ◇ y) ◇ (y ◇ (z ◇ y)))) :=
        congrArg (fun t => ((z ◇ y) ◇ x) ◇ (x ◇ t)) (h y z y)
      _ = x := (h x (z ◇ y) (y ◇ (z ◇ y))).symm
  obtain ⟨t, ht⟩ := ha.2 a
  let b := (t ◇ t) ◇ a
  have hb : b ◇ a = a := by simpa only [ht] using dual a t t
  refine ⟨b, b ◇ b, fun z => ha.1 (ha.1 ?_)⟩
  have hz := h a b z
  have hh := h a b b
  rw [hb] at hz hh
  exact hz.symm.trans hh

/-- info: 'CentralConstant.bijective_row_gives_constant' does not depend on any axioms -/
#guard_msgs in
#print axioms bijective_row_gives_constant

end CentralConstant
