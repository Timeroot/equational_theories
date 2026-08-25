import equational_theories.Definability.ExactAut7F427

/-!
# Structural certificate sources: `Magma.exactF427`

For each of the following magmas, drawn from the `5` magmas on `Fin 7` whose automorphism group is
exactly the order-`42` group of `Magma.permEF427`, the equations it satisfies that no earlier listed
magma does. Together they are the `106` equations that are worth using as the *source* `L'` of a
`Magma.exactF427` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `5` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrF427`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `62` equations satisfied by `Magma.exactF427 2`, and by no earlier member of the cover. -/
theorem exactF427_satisfies_0 :
    Satisfies (Magma.exactF427 2) [
      73, 75, 118, 125, 222, 229, 264, 274, 437, 504, 510, 633, 640, 704, 716, 883, 910, 917,
      919, 1039, 1046, 1086, 1110, 1232, 1242, 1279, 1323, 1526, 1528, 1722, 1729, 1898, 1925,
      2064, 2101, 2304, 2328, 2330, 2337, 2497, 2506, 2533, 2541, 2673, 2710, 2737, 2744, 2876,
      2903, 2912, 2939, 3059, 3115, 3143, 3279, 3281, 3475, 3482, 3881, 3888, 4074, 4084
    ] := by decide!

/-- `20` equations satisfied by `Magma.exactF427 0`, and by no earlier member of the cover. -/
theorem exactF427_satisfies_1 :
    Satisfies (Magma.exactF427 0) [
      271, 1083, 1239, 1286, 1685, 1895, 2091, 2098, 2257, 2301, 2460, 2504, 2697, 2900, 3105,
      3140, 3954, 4081, 4157, 4658
    ] := by decide!

/-- `16` equations satisfied by `Magma.exactF427 3`, and by no earlier member of the cover. -/
theorem exactF427_satisfies_2 :
    Satisfies (Magma.exactF427 3) [
      63, 427, 467, 667, 870, 1112, 1315, 1489, 1516, 1692, 1922, 2293, 3269, 3345, 3548, 4293
    ] := by decide!

/-- `4` equations satisfied by `Magma.exactF427 1`, and by no earlier member of the cover. -/
theorem exactF427_satisfies_3 :
    Satisfies (Magma.exactF427 1) [
      713, 2063, 2450, 3555
    ] := by decide!

/-- `4` equations satisfied by `Magma.exactF427 4`, and by no earlier member of the cover. -/
theorem exactF427_satisfies_4 :
    Satisfies (Magma.exactF427 4) [
      1119, 1454, 2856, 3961
    ] := by decide!
