import equational_theories.Definability.ExactEnd6AA

/-!
# Term-structural certificate sources: `Magma.end6AA`

For each of the following magmas, drawn from the `12` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`29` monoid of `Magma.endE6AA`, the equations it satisfies that no earlier listed
magma does. Together they are the `38` equations that are worth using as the *source* `L'` of a
`Magma.end6AA` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `8` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end6AA 4`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_0 :
    Satisfies (Magma.end6AA 4) [
      108, 847, 1227, 1250, 1253, 1255, 1263, 4591
    ] := by decide!

/-- `8` equations satisfied by `Magma.end6AA 8`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_1 :
    Satisfies (Magma.end6AA 8) [
      231, 2318, 2351, 2364, 2385, 2406, 2812, 4276
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6AA 1`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_2 :
    Satisfies (Magma.end6AA 1) [
      443, 844, 1042, 3285, 4293
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6AA 3`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_3 :
    Satisfies (Magma.end6AA 3) [
      2571, 2724, 3197, 4105, 4658
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6AA 5`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_4 :
    Satisfies (Magma.end6AA 5) [
      361, 433, 840, 854, 3873
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6AA 9`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_5 :
    Satisfies (Magma.end6AA 9) [
      309, 2712, 2739, 3180, 3467
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AA 6`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_6 :
    Satisfies (Magma.end6AA 6) [
      4093
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AA 10`, and by no earlier member of the cover. -/
theorem end6AA_satisfies_7 :
    Satisfies (Magma.end6AA 10) [
      3262
    ] := by decide!
