import equational_theories.Definability.ExactEnd5W

/-!
# Term-structural certificate sources: `Magma.end5W`

For each of the following magmas, drawn from the `1` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`10` monoid of `Magma.endE5W`, the equations it satisfies that no earlier listed
magma does. Together they are the `6` equations that are worth using as the *source* `L'` of a
`Magma.end5W` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `6` equations satisfied by `Magma.end5W 0`, and by no earlier member of the cover. -/
theorem end5W_satisfies_0 :
    Satisfies (Magma.end5W 0) [
      846, 1519, 2128, 2746, 3558, 3951
    ] := by decide!
