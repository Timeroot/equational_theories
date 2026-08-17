import Lean
import equational_theories.Magma

/-!
# Syntax for definability certificates

`equational_theories.FactsSyntax` provides `Facts G [sats] [refs]` for recording which equations a
single magma satisfies. Definability certificates need two variations on that:

* the magma has to be given *explicitly*, since the certificate magmas are members of a
  parametrized family and are not instances;
* the interesting statement is about a whole family at once — that **no** member of the family
  satisfies a given equation.

`Satisfies M [n₁, …, n_k]` and `FamilyRefutes F [n₁, …, n_k]` do exactly that. Both elaborate to a
plain conjunction, so `decide!` can split them and check each conjunct separately in the kernel.
-/

open Lean Meta Elab Term

/--
`Satisfies M [1, 2]` unfolds to `Equation1 G M ∧ Equation2 G M`, where `M : Magma G` is given
explicitly rather than by instance synthesis.
-/
syntax "Satisfies " term:max " [" num,* "]" : term

/--
`FamilyRefutes F [1, 2]`, for `F : Fin k₁ → ⋯ → Fin k_m → Magma G`, unfolds to
`(∀ i₁ … i_m, ¬ Equation1 G (F i₁ … i_m)) ∧ (∀ i₁ … i_m, ¬ Equation2 G (F i₁ … i_m))`: no member
of the family `F` satisfies any of the listed equations.

Note that the universal quantifiers are *inside* each conjunct, so that the whole statement is a
conjunction of individually decidable propositions.
-/
syntax "FamilyRefutes " term:max " [" num,* "]" : term

/--
`FamilyRefutesBasis F [1, 2]` is `FamilyRefutes F [1, 2]` with each equation tested only at the
`k` *basis* assignments of its `k` variables — the one sending a chosen variable to `1` and the
rest to `0`. So for a two-variable `Equation1` the first conjunct is
`∀ i₁ … i_m, ¬ (Equation1's body at (1, 0) ∧ Equation1's body at (0, 1))`.

This is weaker than `FamilyRefutes` in general and is only useful for families of *linear*
operations over a commutative ring, where it is equivalent: both sides of a law evaluate to a
linear form `Σ pⱼ vⱼ`, the basis assignments read off the `pⱼ` one at a time, and matching
coefficients give the law at every assignment. Deciding it costs `k` law evaluations per family
member instead of `|G| ^ k`, which is the whole point — at `|G| = 487` that is the difference
between a checkable statement and an unusable one.

The direction needed to *use* such a certificate is the trivial one: an inhabitant of
`Equation1 G (F i)` instantiates to each conjunct, as in `fun h ↦ ⟨h 1 0, h 0 1⟩`.
-/
syntax "FamilyRefutesBasis " term:max " [" num,* "]" : term

private def magmaCodomain (e : Expr) : MetaM (Level × Expr) := do
  let e ← whnfR e
  unless e.isAppOfArity ``Magma 1 do throwError "expected a magma, got{indentExpr e}"
  let G := e.appArg!
  let some u := (← getLevel G).dec | throwError "expected G to be a type"
  return (u, G)

elab_rules : term
  | `(Satisfies $M [ $ns,* ]) => do
    let M ← elabTerm M none
    let (u, G) ← magmaCodomain (← inferType M)
    return mkAndN <| (ns.getElems.map fun ⟨s⟩ =>
      mkApp2 (mkConst (.mkSimple s!"Equation{s.toNat}") [u]) G M).toList

elab_rules : term
  | `(FamilyRefutes $F [ $ns,* ]) => do
    let F ← elabTerm F none
    forallTelescopeReducing (← inferType F) fun xs body => do
      let (u, G) ← magmaCodomain body
      let conjs ← ns.getElems.mapM fun ⟨s⟩ => do
        let eq := mkApp2 (mkConst (.mkSimple s!"Equation{s.toNat}") [u]) G (mkAppN F xs)
        mkForallFVars xs (mkApp (mkConst ``Not) eq)
      return mkAndN conjs.toList

elab_rules : term
  | `(FamilyRefutesBasis $F [ $ns,* ]) => do
    let F ← elabTerm F none
    forallTelescopeReducing (← inferType F) fun xs body => do
      let (u, G) ← magmaCodomain body
      let zero ← mkNumeral G 0
      let one ← mkNumeral G 1
      let conjs ← ns.getElems.mapM fun ⟨s⟩ => do
        let eq := mkApp2 (mkConst (.mkSimple s!"Equation{s.toNat}") [u]) G (mkAppN F xs)
        let k ← forallTelescopeReducing eq fun ys _ => pure ys.size
        let basis ← (List.range k).mapM fun j =>
          instantiateForall eq (Array.ofFn fun i : Fin k => if i.val == j then one else zero)
        mkForallFVars xs (mkApp (mkConst ``Not) (mkAndN basis))
      return mkAndN conjs.toList
