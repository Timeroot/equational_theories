import Lean

/-!
# `decide!` for families the kernel cannot walk

`DecideBang.lean` has two tactics for goals that are long conjunctions of statements
`∀ (x … z : Fin n), lhs = rhs`: `decide!`, which builds the decidability instances by type class
synthesis and lets the kernel do the work, and `decideFin!`, which builds them by hand because the
synthesis can cost more than the check. This file adds the third combination, hand-built instances
checked by *native* evaluation, for the certificates whose family is too large for the kernel --
`Definability/Certs/Rigid3*.lean` enumerates all `3 ^ 9` tables on `Fin 3`.

Both hacks are needed, and they are needed for different reasons.

* Splitting the conjunction is what lets the goal elaborate. `native_decide` asks synthesis for a
  single `Decidable` instance for the whole conjunction, and on a certificate listing a hundred-odd
  equations that search does not come back; raising `synthInstance.maxSize` only makes it run
  longer.
* Building the instances by hand is what lets the check finish. Synthesis answers `∀ x : Fin n, _`
  with `Fintype.decidableForallFintype`, which folds over `Finset.univ` and allocates a `Multiset`
  as it goes, while `Nat.decidableForallFin` is a recursion on `Nat`. That is a constant factor
  either way, but `native_decide` does not compile the instance -- it interprets it -- so the
  constant is paid in full.

The tactic is here, rather than in `DecideBang.lean`, so that the generated certificates can be
regenerated without invalidating every module that a `decide!` appears in; the three helpers below
are private there and are repeated for the same reason.
-/

open Lean Elab Tactic Meta

private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

private def splitConjs (e : Lean.Expr) : Array (Lean.Expr) := Id.run do
  let mut e := e
  let mut r := #[]
  while e.isAppOf `And do
    r := r.push e.appFn!.appArg!
    e := e.appArg!
  r := r.push e
  return r

/--
Reduce `p` until its head is one of the shapes `inferDecideFin` understands. Reducible
transparency is not enough: a goal produced by `Definability/CertSyntax.lean` is stated with
`Equationₙ`, a plain `def`, so the quantifiers over the magma's own variables are hidden behind it.
Full `whnf` exposes them, but it would also unfold `Not` into `_ → False` and lose the negation, so
the shapes that are already supported are tested first and only an unrecognised head is unfolded.
-/
private partial def toShape (p : Expr) : MetaM Expr := do
  let p ← whnfR p
  if p.isForall then return p
  match_expr p with
  | True => return p
  | Not _ => return p
  | Eq _ _ _ => return p
  | _ =>
    let p' ← whnf p
    if p' == p then return p else toShape p'

private partial def inferDecideFin (p : Expr) : MetaM Expr := do
  let p ← toShape p
  match p with
  | .forallE i d b bi =>
    match_expr (← whnfR d) with
    | Fin n =>
      let inst ← withLocalDeclD i d fun x => do
        let body := b.instantiate1 x
        let inst ← inferDecideFin body
        mkLambdaFVars #[x] inst
      return mkApp3 (mkConst ``Nat.decidableForallFin) n (.lam i d b bi) inst
    | _ => throwError "Expected Fin n quantifier"
  | _ =>
    match_expr p with
    | True =>
      return mkConst ``True.intro
    | Not p' =>
      let inst ← inferDecideFin p'
      return mkApp2 (mkConst ``instDecidableNot) p' inst
    | Eq t l r =>
      match_expr (← whnfR t) with
      | Fin n =>
        return mkApp3 (mkConst ``instDecidableEqFin) n l r
      | _ => throwError "Expected Fin n equality"
    | _ => throwError "Unsupported proposition {p}"

/--
Like `decideFin!`, but each conjunct is checked by native evaluation rather than by the kernel, and
so rests on `Lean.ofReduceBool`.

Every conjunct costs one `addAndCompile` and one new axiom, so this is meant for a few long
conjunctions rather than for many short ones.
-/
elab "nativeDecideFin!" : tactic => do
  let ref ← getRef
  closeMainGoalUsing `nativeDecideFin fun expectedType _ => do
    let expectedType ← preprocessPropToDecide expectedType
    let expectedTypes := splitConjs expectedType
    let proofs ← expectedTypes.mapM fun expectedType => do
      let s ← inferDecideFin expectedType
      let d := mkApp2 (Lean.mkConst ``Decidable.decide) expectedType s
      match ← Lean.Meta.nativeEqTrue `nativeDecideFin d (axiomDeclRange? := ref) with
      | .notTrue =>
        throwError "tactic 'nativeDecideFin!' evaluated that the proposition\
          {indentExpr expectedType}\nis false"
      | .success prf => return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s prf
    let proof ← proofs.pop.foldrM (mkAppM ``And.intro #[·, ·]) proofs.back!
    return proof
