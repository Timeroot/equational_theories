import equational_theories.Definability.ExactEnd3Q

/-!
# Term-structural certificate sources: `Magma.end3Q`

For each of the following magmas, drawn from the `2` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`9` monoid of `Magma.endE3Q`, the equations it satisfies that no earlier listed
magma does. Together they are the `56` equations that are worth using as the *source* `L'` of a
`Magma.end3Q` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `42` equations satisfied by `Magma.end3Q 0`, and by no earlier member of the cover. -/
theorem end3Q_satisfies_0 :
    Satisfies (Magma.end3Q 0) [
      156, 159, 257, 266, 629, 635, 645, 856, 1431, 1441, 1444, 1447, 1451, 1454, 1640, 1660,
      1867, 1871, 2037, 2040, 2043, 2053, 2056, 2063, 2070, 2655, 2675, 2683, 2691, 2849, 2858,
      2868, 2878, 2886, 2890, 2894, 3061, 3081, 3089, 3097, 3732, 4438
    ] := by decide!

/-- `14` equations satisfied by `Magma.end3Q 1`, and by no earlier member of the cover. -/
theorem end3Q_satisfies_1 :
    Satisfies (Magma.end3Q 1) [
      446, 450, 454, 458, 649, 653, 657, 661, 860, 864, 1437, 1668, 1875, 3728
    ] := by decide!
