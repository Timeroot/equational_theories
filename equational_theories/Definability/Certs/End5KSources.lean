import equational_theories.Definability.ExactEnd5K

/-!
# Term-structural certificate sources: `Magma.end5K`

For each of the following magmas, drawn from the `36` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`13` monoid of `Magma.endE5K`, the equations it satisfies that no earlier listed
magma does. Together they are the `20` equations that are worth using as the *source* `L'` of a
`Magma.end5K` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `10` equations satisfied by `Magma.end5K 4`, and by no earlier member of the cover. -/
theorem end5K_satisfies_0 :
    Satisfies (Magma.end5K 4) [
      258, 1453, 1456, 2044, 2260, 2270, 2653, 2663, 3317, 3320
    ] := by decide!

/-- `10` equations satisfied by `Magma.end5K 28`, and by no earlier member of the cover. -/
theorem end5K_satisfies_1 :
    Satisfies (Magma.end5K 28) [
      72, 909, 916, 1353, 1370, 1525, 2115, 2203, 4192, 4209
    ] := by decide!
