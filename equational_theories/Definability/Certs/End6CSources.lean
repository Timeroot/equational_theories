import equational_theories.Definability.ExactEnd6C

/-!
# Term-structural certificate sources: `Magma.end6C`

For each of the following magmas, drawn from the `10` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`18` monoid of `Magma.endE6C`, the equations it satisfies that no earlier listed
magma does. Together they are the `56` equations that are worth using as the *source* `L'` of a
`Magma.end6C` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `22` equations satisfied by `Magma.end6C 0`, and by no earlier member of the cover. -/
theorem end6C_satisfies_0 :
    Satisfies (Magma.end6C 0) [
      10, 107, 110, 426, 432, 442, 446, 450, 454, 458, 1041, 1048, 1051, 1059, 1063, 1067, 1244,
      1251, 1254, 1262, 1266, 1270
    ] := by decide!

/-- `22` equations satisfied by `Magma.end6C 1`, and by no earlier member of the cover. -/
theorem end6C_satisfies_1 :
    Satisfies (Magma.end6C 1) [
      25, 211, 214, 2259, 2266, 2269, 2277, 2281, 2285, 2462, 2469, 2472, 2480, 2484, 2488, 3052,
      3061, 3071, 3081, 3089, 3093, 3097
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6C 8`, and by no earlier member of the cover. -/
theorem end6C_satisfies_2 :
    Satisfies (Magma.end6C 8) [
      209, 1452, 1453, 2270
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6C 9`, and by no earlier member of the cover. -/
theorem end6C_satisfies_3 :
    Satisfies (Magma.end6C 9) [
      117, 2100, 2115, 2203
    ] := by decide!

/-- `2` equations satisfied by `Magma.end6C 4`, and by no earlier member of the cover. -/
theorem end6C_satisfies_4 :
    Satisfies (Magma.end6C 4) [
      1887, 2037
    ] := by decide!

/-- `2` equations satisfied by `Magma.end6C 6`, and by no earlier member of the cover. -/
theorem end6C_satisfies_5 :
    Satisfies (Magma.end6C 6) [
      1441, 1645
    ] := by decide!
