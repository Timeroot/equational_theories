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
