import equational_theories.Definability.ExactEnd5B

/-!
# Term-structural certificate sources: `Magma.end5B`

For each of the following magmas, drawn from the `16` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`15` monoid of `Magma.endE5B`, the equations it satisfies that no earlier listed
magma does. Together they are the `68` equations that are worth using as the *source* `L'` of a
`Magma.end5B` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `26` equations satisfied by `Magma.end5B 3`, and by no earlier member of the cover. -/
theorem end5B_satisfies_0 :
    Satisfies (Magma.end5B 3) [
      160, 161, 209, 212, 215, 1452, 1453, 1455, 1456, 1457, 1458, 1459, 1460, 2254, 2257, 2260,
      2264, 2267, 2270, 2274, 2278, 2282, 2286, 3059, 3069, 3076
    ] := by decide!

/-- `26` equations satisfied by `Magma.end5B 12`, and by no earlier member of the cover. -/
theorem end5B_satisfies_1 :
    Satisfies (Magma.end5B 12) [
      117, 127, 138, 179, 194, 476, 503, 510, 1278, 1288, 1299, 1315, 1325, 1336, 1353, 1370,
      1387, 1405, 2078, 2100, 2115, 2137, 2152, 2182, 2203, 2227
    ] := by decide!

/-- `5` equations satisfied by `Magma.end5B 1`, and by no earlier member of the cover. -/
theorem end5B_satisfies_2 :
    Satisfies (Magma.end5B 1) [
      1655, 1851, 2460, 2467, 3317
    ] := by decide!

/-- `5` equations satisfied by `Magma.end5B 8`, and by no earlier member of the cover. -/
theorem end5B_satisfies_3 :
    Satisfies (Magma.end5B 8) [
      1085, 1112, 1721, 1897, 4209
    ] := by decide!

/-- `3` equations satisfied by `Magma.end5B 2`, and by no earlier member of the cover. -/
theorem end5B_satisfies_4 :
    Satisfies (Magma.end5B 2) [
      416, 2053, 3918
    ] := by decide!

/-- `3` equations satisfied by `Magma.end5B 13`, and by no earlier member of the cover. -/
theorem end5B_satisfies_5 :
    Satisfies (Magma.end5B 13) [
      1444, 3055, 3512
    ] := by decide!
