import equational_theories.Definability.ExactEnd6N

/-!
# Term-structural certificate sources: `Magma.end6N`

For each of the following magmas, drawn from the `22` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`384` monoid of `Magma.endE6N`, the equations it satisfies that no earlier listed
magma does. Together they are the `41` equations that are worth using as the *source* `L'` of a
`Magma.end6N` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `8` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end6N 5`, and by no earlier member of the cover. -/
theorem end6N_satisfies_0 :
    Satisfies (Magma.end6N 5) [
      152, 153, 1430, 1435, 1634, 1638, 1640, 1641
    ] := by decide!

/-- `8` equations satisfied by `Magma.end6N 8`, and by no earlier member of the cover. -/
theorem end6N_satisfies_1 :
    Satisfies (Magma.end6N 8) [
      156, 166, 1837, 1867, 1931, 1975, 2134, 2161
    ] := by decide!

/-- `6` equations satisfied by `Magma.end6N 7`, and by no earlier member of the cover. -/
theorem end6N_satisfies_2 :
    Satisfies (Magma.end6N 7) [
      283, 2296, 2372, 2469, 2493, 2609
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6N 4`, and by no earlier member of the cover. -/
theorem end6N_satisfies_3 :
    Satisfies (Magma.end6N 4) [
      56, 1021, 1050, 1240, 1243
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6N 13`, and by no earlier member of the cover. -/
theorem end6N_satisfies_4 :
    Satisfies (Magma.end6N 13) [
      1041, 1063, 1664, 1738
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6N 16`, and by no earlier member of the cover. -/
theorem end6N_satisfies_5 :
    Satisfies (Magma.end6N 16) [
      1843, 1845, 2462, 2472
    ] := by decide!

/-- `3` equations satisfied by `Magma.end6N 10`, and by no earlier member of the cover. -/
theorem end6N_satisfies_6 :
    Satisfies (Magma.end6N 10) [
      50, 623, 624
    ] := by decide!

/-- `3` equations satisfied by `Magma.end6N 18`, and by no earlier member of the cover. -/
theorem end6N_satisfies_7 :
    Satisfies (Magma.end6N 18) [
      280, 2946, 3007
    ] := by decide!
