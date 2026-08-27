import equational_theories.Definability.ExactEnd5N

/-!
# Term-structural certificate sources: `Magma.end5N`

For each of the following magmas, drawn from the `67` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`13` monoid of `Magma.endE5N`, the equations it satisfies that no earlier listed
magma does. Together they are the `2` equations that are worth using as the *source* `L'` of a
`Magma.end5N` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.end5N 11`, and by no earlier member of the cover. -/
theorem end5N_satisfies_0 :
    Satisfies (Magma.end5N 11) [
      621
    ] := by decide!

/-- `1` equations satisfied by `Magma.end5N 40`, and by no earlier member of the cover. -/
theorem end5N_satisfies_1 :
    Satisfies (Magma.end5N 40) [
      2919
    ] := by decide!
