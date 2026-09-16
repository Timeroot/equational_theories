import equational_theories.Definability.Reversible

/-!
# Exchanging argument values in the output

`swap(x,y)(x*y)` is an involutive, quantifier-free transformation of every
magma. So is `swap(x,y)(y*x)`. The order of the two equality tests is immaterial.
These observations remove finiteness from existing target-law certificates
for all four syntactic variants of the companion.
-/

open Law Law.MagmaLaw FreeMagma

namespace QFOp

private abbrev x : FreeMagma (Fin 2) := Lf 0
private abbrev y : FreeMagma (Fin 2) := Lf 1

/-- Exchange the arguments in the output, optionally starting with the opposite
operation. `reverse` changes only the order of the two equality tests. -/
def argumentSwap (opposite reverse : Bool) : QFOp :=
  let a := if reverse then y else x
  let b := if reverse then x else y
  let t := if opposite then y ⋆ x else x ⋆ y
  AutBox.iteOf2 t a t b b a t

open scoped Classical in
theorem argumentSwap_apply {G : Type} (M : Magma G) (opposite reverse : Bool) (a b : G) :
    ((argumentSwap opposite reverse).magma M).op a b =
      Equiv.swap a b (if opposite then M.op b a else M.op a b) := by
  cases opposite <;> cases reverse
  · change (if M.op a b = a then b else if M.op a b = b then a else M.op a b) = _
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · change (if M.op a b = b then a else if M.op a b = a then b else M.op a b) = _
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · change (if M.op b a = a then b else if M.op b a = b then a else M.op b a) = _
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · change (if M.op b a = b then a else if M.op b a = a then b else M.op b a) = _
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all

@[simp] theorem argumentSwap_square {G : Type} (M : Magma G)
    (opposite reverse : Bool) (a : G) :
    ((argumentSwap opposite reverse).magma M).op a a = M.op a a := by
  classical
  simp [argumentSwap_apply]

theorem argumentSwap_involutive {G : Type} (M : Magma G) (opposite reverse : Bool) :
    (argumentSwap opposite reverse).magma ((argumentSwap opposite reverse).magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change ((argumentSwap opposite reverse).magma
    ((argumentSwap opposite reverse).magma M)).op a b = M.op a b
  cases opposite <;>
    simp [argumentSwap_apply, Equiv.swap_comm b a]

end QFOp

namespace Law.MagmaLaw

/-- The target-law certificate is the only law-specific obligation. -/
theorem structuralFrom_argumentSwap {L L' : NatMagmaLaw} (opposite reverse : Bool)
    (target : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((QFOp.argumentSwap opposite reverse).magma M) L) :
    L.StructuralFrom L' :=
  structuralFrom_of_qfInverse _ _
    (fun M _ ↦ QFOp.argumentSwap_involutive M opposite reverse) target

end Law.MagmaLaw

namespace ArgumentSwap

/-- Left-identity squares become right-zero squares under the opposite swap. -/
theorem equation312 {G : Type} (M : Magma G) (h : @Equation31 G M) :
    @Equation312 G ((QFOp.argumentSwap true true).magma M) := by
  classical
  intro x y
  simp only [QFOp.argumentSwap_square, QFOp.argumentSwap_apply, if_true]
  rw [← h y x]
  simp

/-- A square fixed on the right gives a two-step diagonal row cycle. -/
theorem equation8 {G : Type} (M : Magma G) (h : @Equation359 G M) :
    @Equation8 G ((QFOp.argumentSwap true true).magma M) := by
  classical
  intro x
  simp only [QFOp.argumentSwap_square, QFOp.argumentSwap_apply, if_true]
  rw [← h x]
  simp

end ArgumentSwap

/-- info: 'QFOp.argumentSwap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QFOp.argumentSwap_involutive

/-! ## Reusing an existing unrestricted target-law certificate

`AutBox.structuralFromFin_iteOf2` already takes its target-law proof over
arbitrary carriers. Only its automorphism-based recovery uses finiteness.
The tactic below extracts that *closed proof term*, checks that its companion
is one of our four involutions, and replaces the recovery argument. It does
not infer an arbitrary-carrier theorem from the finite conclusion, and it
does not rerun the old ATP replay. Lean checks the resulting proof as usual.
-/

open Lean Meta Elab Tactic in
/-- Reuse the unrestricted target-law proof inside a finite two-guard
certificate, replacing its recovery by the argument-swap involution.
Fail closed if the certificate shape, closedness, or companion does not match. -/
elab "recover_argument_swap " certificate:ident : tactic => do
  let name ← realizeGlobalConstNoOverloadWithInfo certificate
  let .thmInfo info ← getConstInfo name
    | throwError "Expected a theorem certificate"
  unless info.levelParams.isEmpty do
    throwError "Expected a monomorphic two-guard certificate"
  let proof ← lambdaTelescope info.value fun _ body => do
    let body := body.consumeMData
    let args := body.getAppArgs
    unless body.getAppFn.isConstOf ``AutBox.structuralFromFin_iteOf2 && args.size ≥ 11 do
      throwError "Expected a direct structuralFromFin_iteOf2 certificate"
    let companion := mkAppN (mkConst ``AutBox.iteOf2) (args.extract 2 9)
    let target := args[10]!
    if companion.hasFVar || target.hasFVar then
      throwError "The companion and target-law proof must be closed, independent of finite-carrier hypotheses"
    for opposite in [false, true] do
      for reverse in [false, true] do
        let o := toExpr opposite
        let r := toExpr reverse
        let candidate ← mkAppM ``QFOp.argumentSwap #[o, r]
        if ← isDefEq companion candidate then
          return ← mkAppOptM ``Law.MagmaLaw.structuralFrom_argumentSwap
            #[some args[0]!, some args[1]!, some o, some r, some target]
    throwError "The certificate companion is not an argument-swap involution"
  unless ← isDefEq (← inferType proof) (← getMainTarget) do
    throwError "The recovered structural statement does not match the goal"
  (← getMainGoal).assign proof
  replaceMainGoal []
