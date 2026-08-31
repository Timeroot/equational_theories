import equational_theories.Definability.ExactEnd5T

/-!
# Term-structural certificate sources: `Magma.end5T`

For each of the following magmas, drawn from the `24` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`108` monoid of `Magma.endE5T`, the equations it satisfies that no earlier listed
magma does. Together they are the `20` equations that are worth using as the *source* `L'` of a
`Magma.end5T` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end5T 9`, and by no earlier member of the cover. -/
theorem end5T_satisfies_0 :
    Satisfies (Magma.end5T 9) [
      1694, 1697, 1705, 1931, 2127, 2134, 2165, 2169
    ] := by decide!

/-- `8` equations satisfied by `Magma.end5T 18`, and by no earlier member of the cover. -/
theorem end5T_satisfies_1 :
    Satisfies (Magma.end5T 18) [
      1435, 1445, 1446, 1448, 1638, 1858, 1868, 1869
    ] := by decide!

/-- `2` equations satisfied by `Magma.end5T 3`, and by no earlier member of the cover. -/
theorem end5T_satisfies_2 :
    Satisfies (Magma.end5T 3) [
      3321, 3324
    ] := by decide!

/-- `2` equations satisfied by `Magma.end5T 7`, and by no earlier member of the cover. -/
theorem end5T_satisfies_3 :
    Satisfies (Magma.end5T 7) [
      4175, 4243
    ] := by decide!
