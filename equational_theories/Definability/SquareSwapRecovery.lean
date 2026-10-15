import equational_theories.Definability.Reversible

/-! Reuse unrestricted target-law proofs from finite certificates whose
companions swap square values. Only the old finite recovery argument is replaced. -/
open Law Law.MagmaLaw FreeMagma
namespace QFOp
private abbrev x : FreeMagma (Fin 2) := Lf 0
private abbrev y : FreeMagma (Fin 2) := Lf 1

/-- All choices of test order and equality orientation for the square swap. -/
def squareSwapVariant (opposite reverse flipFirst flipSecond : Bool) : QFOp :=
  let a := if reverse then y ⋆ y else x ⋆ x
  let b := if reverse then x ⋆ x else y ⋆ y
  let p := if opposite then y ⋆ x else x ⋆ y
  AutBox.iteOf2 (if flipFirst then a else p) (if flipFirst then p else a)
    (if flipSecond then b else p) (if flipSecond then p else b) b a p

open scoped Classical in
theorem squareSwapVariant_apply {G : Type} (M : Magma G)
    (o r u v : Bool) (a b : G) :
    ((squareSwapVariant o r u v).magma M).op a b =
      Equiv.swap (M.op a a) (M.op b b) (if o then M.op b a else M.op a b) := by
  change @QFOp.eval _ M (squareSwapVariant o r u v) ![a,b] = _
  cases o <;> cases r <;> cases u <;> cases v <;>
    simp only [squareSwapVariant, AutBox.iteOf2, QFOp.eval, x, y, Bool.false_eq_true,
      if_false, if_true, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
      Equiv.swap_apply_def] <;>
    split_ifs <;> grind

theorem squareSwapVariant_square {G : Type} (M : Magma G)
    (o r u v : Bool) (a : G) :
    ((squareSwapVariant o r u v).magma M).op a a = M.op a a := by
  classical
  simp [squareSwapVariant_apply]

theorem squareSwapVariant_involutive {G : Type} (M : Magma G) (o r u v : Bool) :
    (squareSwapVariant o r u v).magma ((squareSwapVariant o r u v).magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change ((squareSwapVariant o r u v).magma
    ((squareSwapVariant o r u v).magma M)).op a b = M.op a b
  cases o <;> simp [squareSwapVariant_apply, Equiv.swap_comm (M.op b b)]
end QFOp

namespace Law.MagmaLaw
theorem structuralFrom_squareSwapVariant {A B : NatMagmaLaw} (o r u v : Bool)
    (target : ∀ {G : Type} (M : Magma G), satisfies G A →
      @satisfies _ G ((QFOp.squareSwapVariant o r u v).magma M) B) : B.StructuralFrom A :=
  structuralFrom_of_qfInverse _ _
    (fun M _ => QFOp.squareSwapVariant_involutive M o r u v) target
end Law.MagmaLaw

open Lean Meta Elab Tactic in
/-- Accept only a closed, already proved target-law argument for one of the
sixteen square-swap trees. This never promotes a finite-only target-law proof. -/
elab "recover_square_swap " certificate:ident : tactic => do
  let name ← realizeGlobalConstNoOverloadWithInfo certificate
  let .thmInfo info ← getConstInfo name | throwError "Expected a theorem"
  unless info.levelParams.isEmpty do throwError "Expected a monomorphic certificate"
  let proof ← lambdaTelescope info.value fun _ body => do
    let body := body.consumeMData
    let args := body.getAppArgs
    unless body.getAppFn.isConstOf ``AutBox.structuralFromFin_iteOf2 && args.size ≥ 11 do
      throwError "Expected a direct structuralFromFin_iteOf2 certificate"
    let companion := mkAppN (mkConst ``AutBox.iteOf2) (args.extract 2 9)
    let target := args[10]!
    if companion.hasFVar || target.hasFVar then
      throwError "Companion and target-law proof must be closed, independent of finiteness"
    for o in [false,true] do
      for r in [false,true] do
        for u in [false,true] do
          for v in [false,true] do
            let values := #[toExpr o,toExpr r,toExpr u,toExpr v]
            let candidate ← mkAppM ``QFOp.squareSwapVariant values
            if ← isDefEq companion candidate then
              return ← mkAppOptM ``Law.MagmaLaw.structuralFrom_squareSwapVariant
                #[some args[1]!,some args[0]!,some values[0]!,some values[1]!,
                  some values[2]!,some values[3]!,some target]
    throwError "The certificate does not use a square-swap involution"
  unless ← isDefEq (← inferType proof) (← getMainTarget) do
    throwError "Recovered statement does not match the goal"
  (← getMainGoal).assign proof
  replaceMainGoal []

/-- info: 'QFOp.squareSwapVariant_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QFOp.squareSwapVariant_involutive
