import equational_theories.Definability.Certificates
import equational_theories.Definability.FiniteFlavour

/-!
# Structural certificates: the automorphism group is preserved *exactly*

`Definability/Negative.lean` refutes `L.DefinableFrom L'` by a *one-sided* symmetry argument: a
model `M'` of `L` definable from a model `M` of `L'` inherits the automorphisms of `M`, so
`M.autos ≤ M'.autos`, and a family with no member of `L` in it kills the pair. Nothing there ever
constrains `M'` from *above* — every one of those certificates is happy with an `M'` that is far
more symmetric than `M`, and indeed the most symmetric magmas of all (the projections `x ◇ y = x`
and `x ◇ y = y`, whose automorphism group is the full symmetric group) satisfy enough laws that
the one-sided obstruction can never see them.

`StructuralOnMagma` asks for definability in *both* directions, and that is exactly what turns the
inequality into an equation:

* `M'.Graph` definable in `M` gives `M.autos ≤ M'.autos`;
* `M.Graph` definable in `M'` gives `M'.autos ≤ M.autos`.

So a structural pair has `M.autos = M'.autos`, and a law `L` is structural from `L'` only if every
model of `L'` is matched by a model of `L` **on the same carrier with the same automorphism
group**. This file proves that (`Law.MagmaLaw.not_structuralOnMagma_of_autos_ne`) and packages the
cheapest instance of it.

## The rigid certificate on `Fin 2`

The cheapest instance is the one where the automorphism group is trivial. If `L'` has a **rigid**
two-element model — one with no nontrivial automorphism — then `L` must have a rigid two-element
model too. Twelve of the sixteen magmas on `Fin 2` are rigid (all but the four that ignore an
argument, by `Magma.isEndo_swap_iff`), so both halves of the certificate are a `decide` over a
twelve-member family, and `Definability/Certs/Fin2Rigid*.lean` records them: `2238` equations have
a rigid two-element model and `2456` have none, and every one of those `2238 * 2456` pairs is a
non-structurality fact.

Note that only the *backward* direction of `StructuralOnMagma` is used, so the same argument
refutes the weaker relation "some model of `L` defines a model of `L'`" as well.

This obstruction is invisible to the definability boards: for a rigid `M` the inequality
`M.autos ≤ M'.autos` is vacuous, so none of these pairs is a `DefinableFrom` refutation, and
before this file the structural relations had no refutations of their own at all.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The `12` magmas on `Fin 2` with no nontrivial automorphism. By `Magma.isEndo_swap_iff` these
are all the magmas on `Fin 2` except the four that ignore one of their arguments. -/
@[implicit_reducible]
def fin2Rigid : Fin 12 → Magma (Fin 2)
  | 0 => fin2 0 0 0 0
  | 1 => fin2 0 0 0 1
  | 2 => fin2 0 0 1 0
  | 3 => fin2 0 1 0 0
  | 4 => fin2 0 1 1 0
  | 5 => fin2 0 1 1 1
  | 6 => fin2 1 0 0 0
  | 7 => fin2 1 0 0 1
  | 8 => fin2 1 0 1 1
  | 9 => fin2 1 1 0 1
  | 10 => fin2 1 1 1 0
  | 11 => fin2 1 1 1 1

theorem fin2Rigid_not_isEndo_swap (i : Fin 12) : ¬ (fin2Rigid i).IsEndo ⇑Fin.swap2 := by
  revert i; decide

theorem exists_fin2Rigid_op {op : Fin 2 → Fin 2 → Fin 2}
    (h : ¬ (Magma.mk op).IsEndo ⇑Fin.swap2) : ∃ i : Fin 12, (fin2Rigid i).op = op := by
  revert op; decide

/-- Every rigid magma on `Fin 2` is a member of `Magma.fin2Rigid`. -/
theorem exists_fin2Rigid {M : Magma (Fin 2)} (h : ¬ M.IsEndo ⇑Fin.swap2) :
    ∃ i : Fin 12, fin2Rigid i = M := by
  obtain ⟨op⟩ := M
  obtain ⟨i, hi⟩ := exists_fin2Rigid_op h
  exact ⟨i, congrArg Magma.mk hi⟩

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-! ### The automorphism group is an invariant of a structural pair -/

/-- **The `Aut`-equality obstruction.** A structural companion of `M` has *exactly* the
automorphisms of `M`: the forward definability gives `M.autos ≤ M'.autos` and the backward one
gives `M'.autos ≤ M.autos`. -/
theorem not_structuralOnMagma_of_autos_ne {G : Type} (M : Magma G)
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → M.autos ≠ M'.autos) :
    ¬ StructuralOnMagma L M := by
  rintro ⟨M', hM', hfwd, hback⟩
  exact hL M' hM'
    (le_antisymm (fun _ he ↦ he.of_definable hfwd) (fun _ he ↦ he.of_definable hback))

theorem not_structuralFrom_of_autos_ne {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → M.autos ≠ M'.autos) :
    ¬ L.StructuralFrom L' := fun h ↦ not_structuralOnMagma_of_autos_ne M hL (h M hM)

theorem not_structuralFromFin_of_autos_ne {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L')
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → M.autos ≠ M'.autos) :
    ¬ L.StructuralFromFin L' := fun h ↦ not_structuralOnMagma_of_autos_ne M hL (h M hM)

/-! ### The rigid certificate -/

/-- **Rigidity certificate on `Fin 2`.** If `L'` has a rigid model on `Fin 2` and no rigid magma
on `Fin 2` satisfies `L`, then `L` is not structural from `L'`, even over finite carriers.

Only the backward definability is used: were the structural companion `M'` symmetric, `M` would
inherit its symmetry, and `M` is rigid. -/
theorem not_structuralFromFin_of_fin2Rigid {L L' : Law.NatMagmaLaw} {i : Fin 12}
    (hsrc : @satisfies _ (Fin 2) (Magma.fin2Rigid i) L')
    (htgt : ∀ j : Fin 12, ¬ @satisfies _ (Fin 2) (Magma.fin2Rigid j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', -, hback⟩ := h (Magma.fin2Rigid i) hsrc
  by_cases hs : M'.IsEndo ⇑Fin.swap2
  · exact Magma.fin2Rigid_not_isEndo_swap i (hs.of_definable hback)
  · obtain ⟨j, rfl⟩ := Magma.exists_fin2Rigid hs
    exact htgt j hM'

end Law.MagmaLaw
