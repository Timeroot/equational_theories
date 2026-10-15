import equational_theories.Definability.DiagonalOutputSwap

/-! Reversible output permutations that preserve squares and both cubes.

Leave the diagonal and the entries computing `(a*a)*a` and `a*(a*a)` fixed.
Elsewhere, optionally reverse the inputs and swap two unary output labels.
The labels and the fixed-entry condition survive, so the inverse uses the same
rule (with exchanged label arguments when the inputs were reversed).
-/

open Law Law.MagmaLaw FreeMagma
namespace CubeOutputSwap
private abbrev x : FreeMagma (Fin 2) := Lf 0
private abbrev y : FreeMagma (Fin 2) := Lf 1

/-- Inputs, squares, iterated squares, left cubes, and right cubes, in pairs. -/
def label (i : Fin 10) : FreeMagma (Fin 2) :=
  ![x,y,x ⋆ x,y ⋆ y,(x ⋆ x) ⋆ (x ⋆ x),(y ⋆ y) ⋆ (y ⋆ y),
    (x ⋆ x) ⋆ x,(y ⋆ y) ⋆ y,x ⋆ (x ⋆ x),y ⋆ (y ⋆ y)] i

def value {G : Type} (M : Magma G) (i : Fin 10) (a b : G) : G :=
  ![a,b,M.op a a,M.op b b,M.op (M.op a a) (M.op a a),
    M.op (M.op b b) (M.op b b),M.op (M.op a a) a,M.op (M.op b b) b,
    M.op a (M.op a a),M.op b (M.op b b)] i

def flip (i : Fin 10) : Fin 10 := ![1,0,3,2,5,4,7,6,9,8] i

theorem value_flip {G : Type} (M : Magma G) (i : Fin 10) (a b : G) :
    value M (flip i) a b = value M i b a := by fin_cases i <;> rfl

theorem eval_label {G : Type} (M : Magma G) (i : Fin 10) (a b : G) :
    @FreeMagma.evalInMagma _ _ M ![a,b] (label i) = value M i a b := by
  fin_cases i <;> rfl

def fixedEntry {G : Type} (M : Magma G) (a b : G) : Prop :=
  a = b ∨ M.op a a = b ∨ a = M.op b b

def forward (i j : Fin 10) (o : Bool) : QFOp :=
  let old := .leaf (x ⋆ y)
  let p := if o then y ⋆ x else x ⋆ y
  .ite x y old (.ite (x ⋆ x) y old (.ite x (y ⋆ y) old
    (AutBox.iteOf2 p (label i) p (label j) (label j) (label i) p)))

open scoped Classical in
theorem forward_apply {G : Type} (M : Magma G) (i j : Fin 10) (o : Bool) (a b : G) :
    ((forward i j o).magma M).op a b = if fixedEntry M a b then M.op a b else
      Equiv.swap (value M i a b) (value M j a b) (if o then M.op b a else M.op a b) := by
  change @QFOp.eval _ M (forward i j o) ![a,b] = _
  cases o <;>
    simp only [forward, AutBox.iteOf2, QFOp.eval, x, y, Bool.false_eq_true,
      if_false, if_true, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
      eval_label, Equiv.swap_apply_def, fixedEntry]
  all_goals split_ifs <;> simp_all

@[simp] theorem square {G : Type} (M : Magma G) (i j : Fin 10) (o : Bool) (a : G) :
    ((forward i j o).magma M).op a a = M.op a a := by
  classical
  simp [forward_apply,fixedEntry]

@[simp] theorem left_cube {G : Type} (M : Magma G) (i j : Fin 10) (o : Bool) (a : G) :
    ((forward i j o).magma M).op (M.op a a) a = M.op (M.op a a) a := by
  classical
  simp [forward_apply,fixedEntry]

@[simp] theorem right_cube {G : Type} (M : Magma G) (i j : Fin 10) (o : Bool) (a : G) :
    ((forward i j o).magma M).op a (M.op a a) = M.op a (M.op a a) := by
  classical
  simp [forward_apply,fixedEntry]

@[simp] theorem value_preserved {G : Type} (M : Magma G) (i j k : Fin 10)
    (o : Bool) (a b : G) : value ((forward i j o).magma M) k a b = value M k a b := by
  fin_cases k <;> simp [value]

@[simp] theorem fixedEntry_preserved {G : Type} (M : Magma G) (i j : Fin 10)
    (o : Bool) (a b : G) : fixedEntry ((forward i j o).magma M) a b ↔ fixedEntry M a b := by
  simp [fixedEntry]

theorem fixedEntry_symm {G : Type} (M : Magma G) (a b : G) :
    fixedEntry M a b ↔ fixedEntry M b a := by
  unfold fixedEntry
  grind

def backward (i j : Fin 10) (o : Bool) : QFOp :=
  forward (if o then flip i else i) (if o then flip j else j) o

theorem recover {G : Type} (M : Magma G) (i j : Fin 10) (o : Bool) :
    (backward i j o).magma ((forward i j o).magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change ((backward i j o).magma ((forward i j o).magma M)).op a b = M.op a b
  unfold backward
  by_cases h : fixedEntry M a b
  · simp [forward_apply,h]
  · have hr : ¬ fixedEntry M b a := by rwa [← fixedEntry_symm]
    cases o <;> simp [forward_apply,h,hr,value_flip]
end CubeOutputSwap

namespace Law.MagmaLaw
theorem structuralFrom_cubeOutputSwap {A B : NatMagmaLaw} (i j : Fin 10) (o : Bool)
    (target : ∀ {G : Type} (M : Magma G), satisfies G A →
      @satisfies _ G ((CubeOutputSwap.forward i j o).magma M) B) :
    B.StructuralFrom A :=
  structuralFrom_of_qfInverse _ _ (fun M _ => CubeOutputSwap.recover M i j o) target
end Law.MagmaLaw

/-- info: 'CubeOutputSwap.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CubeOutputSwap.recover
