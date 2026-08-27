import equational_theories.Definability.ExactEnd5P

/-!
# Term-structural certificate sources: `Magma.end5P`

For each of the following magmas, drawn from the `108` magmas on `Fin 5` whose endomorphism monoid
is exactly the order-`10` monoid of `Magma.endE5P`, the equations it satisfies that no earlier
listed magma does. Together they are the `11` equations that are worth using as the *source* `L'` of
a `Magma.end5P` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `6` equations satisfied by `Magma.end5P 25`, and by no earlier member of the cover. -/
theorem end5P_satisfies_0 :
    Satisfies (Magma.end5P 25) [
      2045, 2055, 2062, 2656, 2666, 2883
    ] := by decide!

/-- `5` equations satisfied by `Magma.end5P 40`, and by no earlier member of the cover. -/
theorem end5P_satisfies_1 :
    Satisfies (Magma.end5P 40) [
      690, 947, 960, 1560, 1586
    ] := by decide!
