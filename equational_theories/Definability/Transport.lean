import equational_theories.Definability.Negative

/-!
# Symmetric operations, described by orbit transport

`Definability/Negative.lean` proves the symmetry obstruction: a model of `L'` on `G` hands all of
its automorphisms to whatever model of `L` a definition of `L` from `L'` produces. To use it one
must know the operations on `G` admitting a given group of symmetries, and so far every group has
paid for its own classification lemma -- `Magma.op_eq_of_isEndo_add_one` for the cyclic shift,
`Magma.op_eq_xorOp4` for a double transposition on `Fin 4`, and so on. Each is a separate proof and
each covers exactly one group.

This file replaces all of them with one lemma. The observation is that a classification is nothing
but orbit transport. If `H` is a group of permutations of `Fin n` and `x ◇ y` is `H`-invariant,
then the value at `(x, y)` is determined by the value at any pair in the same `H`-orbit: choosing
`g ∈ H` with `g (a, b) = (x, y)` gives `x ◇ y = g (a ◇ b)`. So an invariant operation is determined
by one value per orbit, and the classification is the function that puts those values back.

That function is `Magma.transport`. Its data is a list `E` of permutations, one orbit
representative `rep i` per orbit, and a table `tr` naming, for each pair `(x, y)`, an orbit and a
group element carrying that orbit's representative to `(x, y)`. All of this is concrete: `htr` says
the table does what it claims and is proved by `decide`.

Two things are deliberately *not* required. `E` need not be closed under composition -- the proof
uses its members one at a time -- and `rep` need not meet the stabilizer condition that makes every
`v` give an invariant operation. Instead `Law.MagmaLaw.not_definableFrom_transport` asks its caller
to rule out only those `v` whose transport really is invariant, which is again a `decide`. So the
family searched is exactly the invariant one, however the data was generated.

The saving is real: for `S₄` fixing a point of `Fin 5` there are five orbits, so the search is over
`5 ^ 5 = 3125` tuples rather than the `5 ^ 25` operations, and only `24` of them survive the
invariance test.

## Contents

* `Magma.transport` -- an operation rebuilt from one value per orbit;
* `Magma.op_eq_transport` -- every invariant operation arises this way;
* `Law.MagmaLaw.not_definableFrom_transport` -- the resulting obstruction.
-/

open Law Law.MagmaLaw

namespace Magma

variable {n m k : ℕ}

/-- The operation on `Fin n` whose value at `(x, y)` is obtained by transporting the value `v i`
along the permutation `E j`, where `(i, j) = tr x y`. When `tr` and `E` describe the orbits of a
group of symmetries, this runs over exactly the invariant operations; see `Magma.op_eq_transport`.
-/
def transport (E : Fin k → Fin n → Fin n) (tr : Fin n → Fin n → Fin m × Fin k)
    (v : Fin m → Fin n) : Fin n → Fin n → Fin n :=
  fun x y ↦ E (tr x y).2 (v (tr x y).1)

/-- **Orbit transport.** If every `E i` is an endomorphism of `M` and `tr` really does carry the
representative `rep (tr x y).1` to `(x, y)`, then `M` is determined by its values at the
representatives. -/
theorem op_eq_transport {M : Magma (Fin n)} {E : Fin k → Fin n → Fin n}
    {rep : Fin m → Fin n × Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    (hE : ∀ i, M.IsEndo (E i))
    (htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧ E (tr x y).2 (rep (tr x y).1).2 = y) :
    M.op = transport E tr (fun i ↦ M.op (rep i).1 (rep i).2) := by
  funext x y
  obtain ⟨h₁, h₂⟩ := htr x y
  show M.op x y = E (tr x y).2 (M.op (rep (tr x y).1).1 (rep (tr x y).1).2)
  rw [hE (tr x y).2, h₁, h₂]

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β} {n m k : ℕ}

/-- **Symmetry obstruction by orbit transport.** Suppose `L'` has a model `M` on `Fin n` admitting
each `E i` as an automorphism -- invertibility comes from `Einv`, which is why this refutes full
first-order definability and not merely term-definability. Suppose further that `tr` describes the
orbits of the `E i` on ordered pairs, and that no `E`-invariant operation built by transport
satisfies `L`. Then `L` is not definable from `L'`.

Everything but `hM` is decidable on a concrete carrier: `hl`, `hr`, `hE` and `htr` by `decide`, and
`hL` by `native_decide` over the `n ^ m` tuples. -/
theorem not_definableFrom_transport (M : Magma (Fin n)) (hM : satisfies (Fin n) L')
    (E Einv : Fin k → Fin n → Fin n) (rep : Fin m → Fin n × Fin n)
    (tr : Fin n → Fin n → Fin m × Fin k)
    (hl : ∀ i, Function.LeftInverse (Einv i) (E i))
    (hr : ∀ i, Function.RightInverse (Einv i) (E i))
    (hE : ∀ i, M.IsEndo (E i))
    (htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧ E (tr x y).2 (rep (tr x y).1).2 = y)
    (hL : ∀ v : Fin m → Fin n,
        (∀ i, (Magma.mk (Magma.transport E tr v)).IsEndo (E i)) →
        ¬ @satisfies _ (Fin n) (Magma.mk (Magma.transport E tr v)) L) :
    ¬ L.DefinableFrom L' := by
  intro h
  obtain ⟨M', hM', hd⟩ := h M hM
  have hE' : ∀ i, M'.IsEndo (E i) := fun i ↦
    Magma.IsEndo.of_definable (e := ⟨E i, Einv i, hl i, hr i⟩) hd (hE i)
  have key : Magma.mk (Magma.transport E tr fun i ↦ M'.op (rep i).1 (rep i).2) = M' := by
    cases M' with
    | mk op => exact congrArg Magma.mk (Magma.op_eq_transport (M := Magma.mk op) (rep := rep) hE'
        htr).symm
  refine hL (fun i ↦ M'.op (rep i).1 (rep i).2) ?_ ?_ <;> rw [key]
  · exact hE'
  · exact hM'

end Law.MagmaLaw
