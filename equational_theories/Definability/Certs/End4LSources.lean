import equational_theories.Definability.ExactEnd4L

/-!
# Term-structural certificate sources: `Magma.end4L`

For each of the following magmas, drawn from the `2` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`16` monoid of `Magma.endE4L`, the equations it satisfies that no earlier listed
magma does. Together they are the `33` equations that are worth using as the *source* `L'` of a
`Magma.end4L` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `22` equations satisfied by `Magma.end4L 1`, and by no earlier member of the cover. -/
theorem end4L_satisfies_0 :
    Satisfies (Magma.end4L 1) [
      238, 257, 1668, 1875, 1897, 2347, 2381, 2398, 2415, 2513, 2550, 2601, 2618, 2655, 2716,
      2753, 2778, 2804, 2821, 2849, 3108, 3803
    ] := by decide!

/-- `11` equations satisfied by `Magma.end4L 0`, and by no earlier member of the cover. -/
theorem end4L_satisfies_1 :
    Satisfies (Magma.end4L 0) [
      52, 103, 428, 629, 837, 852, 1237, 1655, 1660, 1871, 3723
    ] := by decide!
