import equational_theories.Definability.ExactEnd4H

/-!
# Term-structural certificate sources: `Magma.end4H`

For each of the following magmas, drawn from the `56` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`4` monoid of `Magma.endE4H`, the equations it satisfies that no earlier listed
magma does. Together they are the `36` equations that are worth using as the *source* `L'` of a
`Magma.end4H` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `13` equations satisfied by `Magma.end4H 11`, and by no earlier member of the cover. -/
theorem end4H_satisfies_0 :
    Satisfies (Magma.end4H 11) [
      1656, 1659, 1661, 1663, 1852, 1862, 1872, 1874, 2463, 2473, 2477, 2481, 2489
    ] := by decide!

/-- `13` equations satisfied by `Magma.end4H 19`, and by no earlier member of the cover. -/
theorem end4H_satisfies_1 :
    Satisfies (Magma.end4H 19) [
      1096, 1133, 1150, 1167, 1202, 1742, 1763, 1797, 1816, 1912, 1979, 2000, 2024
    ] := by decide!

/-- `6` equations satisfied by `Magma.end4H 3`, and by no earlier member of the cover. -/
theorem end4H_satisfies_2 :
    Satisfies (Magma.end4H 3) [
      156, 1644, 1650, 1867, 2040, 2070
    ] := by decide!

/-- `4` equations satisfied by `Magma.end4H 27`, and by no earlier member of the cover. -/
theorem end4H_satisfies_3 :
    Satisfies (Magma.end4H 27) [
      153, 1431, 1437, 1853
    ] := by decide!
