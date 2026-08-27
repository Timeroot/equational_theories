import equational_theories.Definability.ExactEnd5R

/-!
# Term-structural certificate sources: `Magma.end5R`

For each of the following magmas, drawn from the `76` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`17` monoid of `Magma.endE5R`, the equations it satisfies that no earlier listed
magma does. Together they are the `13` equations that are worth using as the *source* `L'` of a
`Magma.end5R` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `12` equations satisfied by `Magma.end5R 54`, and by no earlier member of the cover. -/
theorem end5R_satisfies_0 :
    Satisfies (Magma.end5R 54) [
      2567, 2919, 2956, 2973, 2990, 3024, 3122, 3149, 3159, 3193, 3210, 3227
    ] := by decide!

/-- `1` equations satisfied by `Magma.end5R 0`, and by no earlier member of the cover. -/
theorem end5R_satisfies_1 :
    Satisfies (Magma.end5R 0) [
      1024
    ] := by decide!
