import equational_theories.Definability.ExactEnd7C

/-!
# Term-structural certificate sources: `Magma.end7C`

For each of the following magmas, drawn from the `100` magmas on `Fin 7` whose endomorphism monoid
is exactly the order-`25` monoid of `Magma.endE7C`, the equations it satisfies that no earlier
listed magma does. Together they are the `19` equations that are worth using as the *source* `L'` of
a `Magma.end7C` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `7` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd7`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `4` equations satisfied by `Magma.end7C 68`, and by no earlier member of the cover. -/
theorem end7C_satisfies_0 :
    Satisfies (Magma.end7C 68) [
      280, 2899, 2946, 3007
    ] := by decide!

/-- `4` equations satisfied by `Magma.end7C 94`, and by no earlier member of the cover. -/
theorem end7C_satisfies_1 :
    Satisfies (Magma.end7C 94) [
      1435, 1638, 1931, 2134
    ] := by decide!

/-- `3` equations satisfied by `Magma.end7C 14`, and by no earlier member of the cover. -/
theorem end7C_satisfies_2 :
    Satisfies (Magma.end7C 14) [
      56, 1021, 1050
    ] := by decide!

/-- `3` equations satisfied by `Magma.end7C 22`, and by no earlier member of the cover. -/
theorem end7C_satisfies_3 :
    Satisfies (Magma.end7C 22) [
      615, 623, 624
    ] := by decide!

/-- `3` equations satisfied by `Magma.end7C 36`, and by no earlier member of the cover. -/
theorem end7C_satisfies_4 :
    Satisfies (Magma.end7C 36) [
      283, 2493, 2609
    ] := by decide!

/-- `1` equations satisfied by `Magma.end7C 52`, and by no earlier member of the cover. -/
theorem end7C_satisfies_5 :
    Satisfies (Magma.end7C 52) [
      2808
    ] := by decide!

/-- `1` equations satisfied by `Magma.end7C 76`, and by no earlier member of the cover. -/
theorem end7C_satisfies_6 :
    Satisfies (Magma.end7C 76) [
      861
    ] := by decide!
