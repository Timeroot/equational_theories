import equational_theories.Definability.ExactEnd6W

/-!
# Term-structural certificate sources: `Magma.end6W`

For each of the following magmas, drawn from the `16` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`32` monoid of `Magma.endE6W`, the equations it satisfies that no earlier listed
magma does. Together they are the `28` equations that are worth using as the *source* `L'` of a
`Magma.end6W` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `9` equations satisfied by `Magma.end6W 6`, and by no earlier member of the cover. -/
theorem end6W_satisfies_0 :
    Satisfies (Magma.end6W 6) [
      1431, 1630, 1633, 1635, 1833, 1839, 1848, 1849, 4286
    ] := by decide!

/-- `9` equations satisfied by `Magma.end6W 12`, and by no earlier member of the cover. -/
theorem end6W_satisfies_1 :
    Satisfies (Magma.end6W 12) [
      1681, 1684, 1687, 1701, 1884, 1894, 1958, 2040, 4642
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6W 0`, and by no earlier member of the cover. -/
theorem end6W_satisfies_2 :
    Satisfies (Magma.end6W 0) [
      156, 1644, 1650, 1867, 2070
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6W 10`, and by no earlier member of the cover. -/
theorem end6W_satisfies_3 :
    Satisfies (Magma.end6W 10) [
      153, 1437, 1640, 1834, 1853
    ] := by decide!
