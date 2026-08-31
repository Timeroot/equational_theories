import equational_theories.Definability.ExactEnd5Y

/-!
# Term-structural certificate sources: `Magma.end5Y`

For each of the following magmas, drawn from the `15` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`10` monoid of `Magma.endE5Y`, the equations it satisfies that no earlier listed
magma does. Together they are the `1` equations that are worth using as the *source* `L'` of a
`Magma.end5Y` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.end5Y 10`, and by no earlier member of the cover. -/
theorem end5Y_satisfies_0 :
    Satisfies (Magma.end5Y 10) [
      4229
    ] := by decide!
