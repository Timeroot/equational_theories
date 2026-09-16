import equational_theories.Definability.AutBox2

/-!
# Reversible case-defined companions

An explicit inverse proves structural definability on **arbitrary** carriers.
This is stronger than comparing automorphism groups on finite carriers, and
avoids replaying that comparison separately for each source law.

The main example swaps the two square values `x ◇ x` and `y ◇ y` in the
output `x ◇ y`. It leaves the square map unchanged, so performing the same
swap again recovers the original operation. The opposite companion is also
an involution. No source law or cancellation assumption is needed.

The final helpers cover the degenerate case: a decision tree that merely
returns `x ◇ y` or `y ◇ x`. Arbitrarily complicated guards do not make its
automorphism obligation more complicated.
-/

open Law Law.MagmaLaw FreeMagma

namespace Law.MagmaLaw

/-- A definable companion with an explicit definable inverse is structural;
both the target law and recovery are checked on the original source models. -/
theorem structuralFrom_of_qfInverse {L L' : NatMagmaLaw} (q r : QFOp)
    (recover : ∀ {G : Type} (M : Magma G), satisfies G L' → r.magma (q.magma M) = M)
    (target : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G (q.magma M) L) : L.StructuralFrom L' := by
  intro G M hM
  refine ⟨q.magma M, target M hM, q.definable_graph M, ?_⟩
  simpa only [recover M hM] using r.definable_graph (q.magma M)

end Law.MagmaLaw

namespace QFOp

private abbrev x : FreeMagma (Fin 2) := Lf 0
private abbrev y : FreeMagma (Fin 2) := Lf 1

/-- Swap the two square values in each output, leaving every other value alone. -/
def squareSwap : QFOp :=
  AutBox.iteOf2 (x ⋆ x) (x ⋆ y) (x ⋆ y) (y ⋆ y) (y ⋆ y) (x ⋆ x) (x ⋆ y)

/-- The same output swap, starting with the opposite operation. -/
def squareSwapOpposite : QFOp :=
  AutBox.iteOf2 (x ⋆ x) (y ⋆ x) (y ⋆ x) (y ⋆ y) (y ⋆ y) (x ⋆ x) (y ⋆ x)

open scoped Classical in
theorem squareSwap_apply {G : Type} (M : Magma G) (a b : G) :
    (squareSwap.magma M).op a b = Equiv.swap (M.op a a) (M.op b b) (M.op a b) := by
  change (if M.op a a = M.op a b then M.op b b
    else if M.op a b = M.op b b then M.op a a else M.op a b) = _
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all

open scoped Classical in
theorem squareSwapOpposite_apply {G : Type} (M : Magma G) (a b : G) :
    (squareSwapOpposite.magma M).op a b = Equiv.swap (M.op a a) (M.op b b) (M.op b a) := by
  change (if M.op a a = M.op b a then M.op b b
    else if M.op b a = M.op b b then M.op a a else M.op b a) = _
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all

@[simp] theorem squareSwap_square {G : Type} (M : Magma G) (a : G) :
    (squareSwap.magma M).op a a = M.op a a := by
  classical
  simp [squareSwap_apply]

@[simp] theorem squareSwapOpposite_square {G : Type} (M : Magma G) (a : G) :
    (squareSwapOpposite.magma M).op a a = M.op a a := by
  classical
  simp [squareSwapOpposite_apply]

theorem squareSwap_involutive {G : Type} (M : Magma G) :
    squareSwap.magma (squareSwap.magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change (squareSwap.magma (squareSwap.magma M)).op a b = M.op a b
  rw [squareSwap_apply, squareSwap_square, squareSwap_square, squareSwap_apply]
  simp

theorem squareSwapOpposite_involutive {G : Type} (M : Magma G) :
    squareSwapOpposite.magma (squareSwapOpposite.magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change (squareSwapOpposite.magma (squareSwapOpposite.magma M)).op a b = M.op a b
  rw [squareSwapOpposite_apply, squareSwapOpposite_square,
    squareSwapOpposite_square, squareSwapOpposite_apply, Equiv.swap_comm (M.op b b)]
  simp

end QFOp

namespace Law.MagmaLaw

theorem structuralFrom_squareSwap {L L' : NatMagmaLaw}
    (target : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G (QFOp.squareSwap.magma M) L) : L.StructuralFrom L' :=
  structuralFrom_of_qfInverse _ _ (fun M _ ↦ QFOp.squareSwap_involutive M) target

theorem structuralFrom_squareSwapOpposite {L L' : NatMagmaLaw}
    (target : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G (QFOp.squareSwapOpposite.magma M) L) : L.StructuralFrom L' :=
  structuralFrom_of_qfInverse _ _ (fun M _ ↦ QFOp.squareSwapOpposite_involutive M) target

end Law.MagmaLaw

namespace AutBox

/-- Identify the opaque operation in a guard certificate with its decision tree. -/
theorem iteOf2_eq_of_clauses {G : Type} (M : Magma G)
    (P Q R S A B C : FreeMagma (Fin 2)) (k : G → G → G)
    (h₁ : ∀ a b, @evalInMagma _ _ M ![a,b] P = @evalInMagma _ _ M ![a,b] Q →
      k a b = @evalInMagma _ _ M ![a,b] A)
    (h₂ : ∀ a b, @evalInMagma _ _ M ![a,b] P ≠ @evalInMagma _ _ M ![a,b] Q →
      @evalInMagma _ _ M ![a,b] R = @evalInMagma _ _ M ![a,b] S →
      k a b = @evalInMagma _ _ M ![a,b] B)
    (h₃ : ∀ a b, @evalInMagma _ _ M ![a,b] P ≠ @evalInMagma _ _ M ![a,b] Q →
      @evalInMagma _ _ M ![a,b] R ≠ @evalInMagma _ _ M ![a,b] S →
      k a b = @evalInMagma _ _ M ![a,b] C) (a b : G) :
    k a b = ((iteOf2 P Q R S A B C).magma M).op a b := by
  classical
  rw [iteOf2_apply]
  split_ifs with h h'
  · exact h₁ a b h
  · exact h₂ a b h h'
  · exact h₃ a b h h'

/-- If the tree is just the original operation, the automorphism obligation is immediate. -/
theorem guardAut2_of_eq_op {L : NatMagmaLaw} {P Q R S A B C : FreeMagma (Fin 2)}
    (normal : ∀ {G : Type} (M : Magma G) (a b : G),
      ((iteOf2 P Q R S A B C).magma M).op a b = M.op a b) :
    GuardAut2 P Q R S A B C L := by
  intro G _ M _ σ _ _ _ k h₁ h₂ h₃ hcom a b
  have hk x y := (iteOf2_eq_of_clauses M P Q R S A B C k h₁ h₂ h₃ x y).trans (normal M x y)
  simpa only [hk] using hcom a b

/-- Taking the opposite operation also preserves exactly the same automorphisms. -/
theorem guardAut2_of_eq_opposite {L : NatMagmaLaw} {P Q R S A B C : FreeMagma (Fin 2)}
    (normal : ∀ {G : Type} (M : Magma G) (a b : G),
      ((iteOf2 P Q R S A B C).magma M).op a b = M.op b a) :
    GuardAut2 P Q R S A B C L := by
  intro G _ M _ σ _ _ _ k h₁ h₂ h₃ hcom a b
  have hk x y := (iteOf2_eq_of_clauses M P Q R S A B C k h₁ h₂ h₃ x y).trans (normal M x y)
  simpa only [hk] using hcom b a

end AutBox

/-- info: 'QFOp.squareSwap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QFOp.squareSwap_involutive

/-- info: 'QFOp.squareSwapOpposite_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QFOp.squareSwapOpposite_involutive
