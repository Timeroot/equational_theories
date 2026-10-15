import equational_theories.Definability.DiagonalOutputSwap

/-! A partial transpose controlled only by the square map and its iterates.
The condition is symmetrized in its two arguments. Squares are unchanged, so
the condition survives, and applying the construction twice recovers the magma. -/
open Law Law.MagmaLaw FreeMagma
namespace DiagonalTranspose

inductive Condition where
  | eq (i j : Fin 6)
  | and (p q : Condition)
  | or (p q : Condition)
  | not (p : Condition)
  deriving Inhabited

def holds {G : Type} (M : Magma G) (a b : G) : Condition → Prop
  | .eq i j => DiagonalOutputSwap.value M i a b = DiagonalOutputSwap.value M j a b
  | .and p q => holds M a b p ∧ holds M a b q
  | .or p q => holds M a b p ∨ holds M a b q
  | .not p => ¬ holds M a b p

def mirror : Condition → Condition
  | .eq i j => .eq (DiagonalOutputSwap.flip i) (DiagonalOutputSwap.flip j)
  | .and p q => .and (mirror p) (mirror q)
  | .or p q => .or (mirror p) (mirror q)
  | .not p => .not (mirror p)

theorem holds_mirror {G : Type} (M : Magma G) (a b : G) (c : Condition) :
    holds M a b (mirror c) ↔ holds M b a c := by
  induction c <;> simp_all [mirror, holds, DiagonalOutputSwap.value_flip]

def branch : Condition → QFOp → QFOp → QFOp
  | .eq i j, yes, no => .ite (DiagonalOutputSwap.label i) (DiagonalOutputSwap.label j) yes no
  | .and p q, yes, no => branch p (branch q yes no) no
  | .or p q, yes, no => branch p yes (branch q yes no)
  | .not p, yes, no => branch p no yes

open scoped Classical in
theorem branch_apply {G : Type} (M : Magma G) (a b : G) (c : Condition) (yes no : QFOp) :
    ((branch c yes no).magma M).op a b =
      if holds M a b c then (yes.magma M).op a b else (no.magma M).op a b := by
  change @QFOp.eval _ M (branch c yes no) ![a,b] =
    if holds M a b c then @QFOp.eval _ M yes ![a,b] else @QFOp.eval _ M no ![a,b]
  induction c generalizing yes no with
  | eq i j =>
    simp only [branch, QFOp.eval, DiagonalOutputSwap.eval_label, holds]
    split_ifs <;> rfl
  | and p q hp hq =>
    simp only [branch, hp, hq, holds]
    split_ifs <;> simp_all
  | or p q hp hq =>
    simp only [branch, hp, hq, holds]
    split_ifs <;> simp_all
  | not p hp =>
    simp only [branch, hp, holds]
    split_ifs <;> simp_all

def forward (c : Condition) : QFOp :=
  branch (.or c (mirror c)) (.leaf (Lf 0 ⋆ Lf 1)) (.leaf (Lf 1 ⋆ Lf 0))

def guard {G : Type} (M : Magma G) (a b : G) (c : Condition) : Prop :=
  holds M a b c ∨ holds M b a c

open scoped Classical in
theorem forward_apply {G : Type} (M : Magma G) (a b : G) (c : Condition) :
    ((forward c).magma M).op a b = if guard M a b c then M.op a b else M.op b a := by
  unfold forward
  rw [branch_apply]
  simp only [holds, holds_mirror, guard]
  change (if holds M a b c ∨ holds M b a c then M.op a b else M.op b a) = _
  split_ifs <;> rfl

@[simp] theorem square {G : Type} (M : Magma G) (c : Condition) (a : G) :
    ((forward c).magma M).op a a = M.op a a := by
  classical
  simp [forward_apply]

@[simp] theorem value_preserved {G : Type} (M : Magma G) (c : Condition)
    (i : Fin 6) (a b : G) :
    DiagonalOutputSwap.value ((forward c).magma M) i a b =
      DiagonalOutputSwap.value M i a b := by
  fin_cases i <;> simp [DiagonalOutputSwap.value]

@[simp] theorem holds_preserved {G : Type} (M : Magma G) (c d : Condition) (a b : G) :
    holds ((forward c).magma M) a b d ↔ holds M a b d := by
  induction d <;> simp_all [holds]

@[simp] theorem guard_preserved {G : Type} (M : Magma G) (c d : Condition) (a b : G) :
    guard ((forward c).magma M) a b d ↔ guard M a b d := by simp [guard]

theorem recover {G : Type} (M : Magma G) (c : Condition) :
    (forward c).magma ((forward c).magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change ((forward c).magma ((forward c).magma M)).op a b = M.op a b
  by_cases h : guard M a b c
  · simp [forward_apply, h]
  · have hr : ¬ guard M b a c := by simpa only [guard, or_comm] using h
    simp [forward_apply, h, hr]

end DiagonalTranspose

namespace Law.MagmaLaw
theorem structuralFrom_diagonalTranspose {A B : NatMagmaLaw} (c : DiagonalTranspose.Condition)
    (target : ∀ {G : Type} (M : Magma G), satisfies G A →
      @satisfies _ G ((DiagonalTranspose.forward c).magma M) B) : B.StructuralFrom A :=
  structuralFrom_of_qfInverse _ _ (fun M _ => DiagonalTranspose.recover M c) target
end Law.MagmaLaw

/-- info: 'DiagonalTranspose.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagonalTranspose.recover
