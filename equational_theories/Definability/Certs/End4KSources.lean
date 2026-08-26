import equational_theories.Definability.ExactEnd4K

/-!
# Term-structural certificate sources: `Magma.end4K`

For each of the following magmas, drawn from the `6` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`8` monoid of `Magma.endE4K`, the equations it satisfies that no earlier listed
magma does. Together they are the `15` equations that are worth using as the *source* `L'` of a
`Magma.end4K` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `5` equations satisfied by `Magma.end4K 1`, and by no earlier member of the cover. -/
theorem end4K_satisfies_0 :
    Satisfies (Magma.end4K 1) [
      166, 1681, 2161, 3897, 3952
    ] := by decide!

/-- `4` equations satisfied by `Magma.end4K 3`, and by no earlier member of the cover. -/
theorem end4K_satisfies_1 :
    Satisfies (Magma.end4K 3) [
      1443, 1630, 1633, 3521
    ] := by decide!

/-- `3` equations satisfied by `Magma.end4K 2`, and by no earlier member of the cover. -/
theorem end4K_satisfies_2 :
    Satisfies (Magma.end4K 2) [
      1884, 1958, 2093
    ] := by decide!

/-- `3` equations satisfied by `Magma.end4K 4`, and by no earlier member of the cover. -/
theorem end4K_satisfies_3 :
    Satisfies (Magma.end4K 4) [
      1430, 1833, 3460
    ] := by decide!
