import equational_theories.Definability.ExactEnd5H

/-!
# Term-structural certificate sources: `Magma.end5H`

For each of the following magmas, drawn from the `4` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`19` monoid of `Magma.endE5H`, the equations it satisfies that no earlier listed
magma does. Together they are the `126` equations that are worth using as the *source* `L'` of a
`Magma.end5H` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `63` equations satisfied by `Magma.end5H 0`, and by no earlier member of the cover. -/
theorem end5H_satisfies_0 :
    Satisfies (Magma.end5H 0) [
      9, 49, 51, 103, 152, 209, 308, 416, 418, 420, 421, 422, 423, 424, 425, 621, 625, 626, 627,
      628, 824, 827, 828, 829, 830, 831, 1024, 1027, 1030, 1033, 1034, 1230, 1233, 1234, 1235,
      1236, 1237, 1428, 1430, 1452, 1453, 1630, 1633, 1833, 1839, 2036, 2254, 2257, 2260, 2452,
      2460, 2467, 2650, 2863, 3257, 3320, 3460, 3723, 3868, 3921, 4268, 4282, 4395
    ] := by decide!

/-- `63` equations satisfied by `Magma.end5H 2`, and by no earlier member of the cover. -/
theorem end5H_satisfies_1 :
    Satisfies (Magma.end5H 2) [
      28, 117, 166, 238, 260, 290, 364, 669, 879, 1055, 1085, 1112, 1278, 1315, 1353, 1478, 1681,
      1701, 1884, 1958, 2050, 2100, 2115, 2161, 2273, 2310, 2347, 2381, 2398, 2415, 2513, 2550,
      2567, 2601, 2618, 2679, 2716, 2753, 2787, 2804, 2821, 2882, 2919, 2956, 2990, 3024, 3055,
      3085, 3122, 3149, 3159, 3193, 3210, 3227, 3474, 3533, 3803, 3897, 4100, 4192, 4385, 4587,
      4666
    ] := by decide!
