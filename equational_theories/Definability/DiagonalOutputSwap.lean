import equational_theories.Definability.Reversible
import Mathlib.Tactic.FinCases

/-! Reversible output swaps that preserve the diagonal. The labels may be an
argument, its square, or its iterated square. No law or finiteness is assumed. -/
open Law Law.MagmaLaw FreeMagma
namespace DiagonalOutputSwap
private abbrev x : FreeMagma (Fin 2) := Lf 0
private abbrev y : FreeMagma (Fin 2) := Lf 1

def label (i : Fin 6) : FreeMagma (Fin 2) :=
  ![x,y,x ⋆ x,y ⋆ y,(x ⋆ x) ⋆ (x ⋆ x),(y ⋆ y) ⋆ (y ⋆ y)] i

def value {G : Type} (M : Magma G) (i : Fin 6) (a b : G) : G :=
  ![a,b,M.op a a,M.op b b,M.op (M.op a a) (M.op a a),
    M.op (M.op b b) (M.op b b)] i

def flip (i : Fin 6) : Fin 6 := ![1,0,3,2,5,4] i

theorem value_flip {G : Type} (M : Magma G) (i : Fin 6) (a b : G) :
    value M (flip i) a b = value M i b a := by fin_cases i <;> rfl

theorem eval_label {G : Type} (M : Magma G) (i : Fin 6) (a b : G) :
    @FreeMagma.evalInMagma _ _ M ![a,b] (label i) = value M i a b := by
  fin_cases i <;> rfl

def forward (i j : Fin 6) (opposite : Bool) : QFOp :=
  let p := if opposite then y ⋆ x else x ⋆ y
  .ite x y (.leaf (x ⋆ x)) (AutBox.iteOf2 p (label i) p (label j) (label j) (label i) p)

open scoped Classical in
theorem forward_apply {G : Type} (M : Magma G) (i j : Fin 6) (o : Bool) (a b : G) :
    ((forward i j o).magma M).op a b =
      if a = b then M.op a a else
        Equiv.swap (value M i a b) (value M j a b) (if o then M.op b a else M.op a b) := by
  change @QFOp.eval _ M (forward i j o) ![a,b] = _
  cases o <;>
    simp only [forward, AutBox.iteOf2, QFOp.eval, x, y, Bool.false_eq_true,
      if_false, if_true, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
      eval_label, Equiv.swap_apply_def]

@[simp] theorem square {G : Type} (M : Magma G) (i j : Fin 6) (o : Bool) (a : G) :
    ((forward i j o).magma M).op a a = M.op a a := by
  classical
  simp [forward_apply]

@[simp] theorem value_preserved {G : Type} (M : Magma G) (i j k : Fin 6)
    (o : Bool) (a b : G) : value ((forward i j o).magma M) k a b = value M k a b := by
  fin_cases k <;> simp [value]

def backward (i j : Fin 6) (o : Bool) : QFOp :=
  forward (if o then flip i else i) (if o then flip j else j) o

theorem recover {G : Type} (M : Magma G) (i j : Fin 6) (o : Bool) :
    (backward i j o).magma ((forward i j o).magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change ((backward i j o).magma ((forward i j o).magma M)).op a b = M.op a b
  unfold backward
  by_cases h : a = b
  · subst b
    simp
  · cases o <;> simp [forward_apply, h, Ne.symm h, value_flip]

end DiagonalOutputSwap

namespace Law.MagmaLaw
theorem structuralFrom_diagonalOutputSwap {A B : NatMagmaLaw} (i j : Fin 6) (o : Bool)
    (target : ∀ {G : Type} (M : Magma G), satisfies G A →
      @satisfies _ G ((DiagonalOutputSwap.forward i j o).magma M) B) :
    B.StructuralFrom A :=
  structuralFrom_of_qfInverse _ _ (fun M _ => DiagonalOutputSwap.recover M i j o) target
end Law.MagmaLaw

/-- info: 'DiagonalOutputSwap.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagonalOutputSwap.recover

namespace DiagonalOutputSwap
open scoped Classical

theorem case_left {G : Type} (M : Magma G) (i j : Fin 6) (o : Bool) (a b : G)
    (hne : a ≠ b) (h : (if o then M.op b a else M.op a b) = value M i a b) :
    ((forward i j o).magma M).op a b = value M j a b := by
  simp [forward_apply,hne,h]

theorem case_right {G : Type} (M : Magma G) (i j : Fin 6) (o : Bool) (a b : G)
    (hne : a ≠ b) (h : (if o then M.op b a else M.op a b) = value M j a b) :
    ((forward i j o).magma M).op a b = value M i a b := by
  simp [forward_apply,hne,h]

theorem case_other {G : Type} (M : Magma G) (i j : Fin 6) (o : Bool) (a b : G)
    (hne : a ≠ b)
    (hi : (if o then M.op b a else M.op a b) ≠ value M i a b)
    (hj : (if o then M.op b a else M.op a b) ≠ value M j a b) :
    ((forward i j o).magma M).op a b = (if o then M.op b a else M.op a b) := by
  simp [forward_apply,hne,hi,hj,Equiv.swap_apply_def]
end DiagonalOutputSwap
