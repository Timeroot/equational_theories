import equational_theories.Definability.ExactEnd6S

/-!
# Term-structural certificate sources: `Magma.end6S`

For each of the following magmas, drawn from the `24` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`30` monoid of `Magma.endE6S`, the equations it satisfies that no earlier listed
magma does. Together they are the `50` equations that are worth using as the *source* `L'` of a
`Magma.end6S` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `8` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `22` equations satisfied by `Magma.end6S 11`, and by no earlier member of the cover. -/
theorem end6S_satisfies_0 :
    Satisfies (Magma.end6S 11) [
      25, 211, 214, 2259, 2266, 2269, 2277, 2281, 2285, 2462, 2469, 2472, 2480, 2484, 2488, 3052,
      3061, 3071, 3081, 3089, 3093, 3097
    ] := by decide!

/-- `18` equations satisfied by `Magma.end6S 0`, and by no earlier member of the cover. -/
theorem end6S_satisfies_1 :
    Satisfies (Magma.end6S 0) [
      10, 107, 110, 426, 432, 442, 446, 450, 454, 458, 1041, 1048, 1051, 1059, 1063, 1067, 1254,
      1266
    ] := by decide!

/-- `3` equations satisfied by `Magma.end6S 5`, and by no earlier member of the cover. -/
theorem end6S_satisfies_2 :
    Satisfies (Magma.end6S 5) [
      3883, 3989, 3993
    ] := by decide!

/-- `3` equations satisfied by `Magma.end6S 6`, and by no earlier member of the cover. -/
theorem end6S_satisfies_3 :
    Satisfies (Magma.end6S 6) [
      3463, 3513, 3523
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6S 1`, and by no earlier member of the cover. -/
theorem end6S_satisfies_4 :
    Satisfies (Magma.end6S 1) [
      2037
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6S 7`, and by no earlier member of the cover. -/
theorem end6S_satisfies_5 :
    Satisfies (Magma.end6S 7) [
      3524
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6S 14`, and by no earlier member of the cover. -/
theorem end6S_satisfies_6 :
    Satisfies (Magma.end6S 14) [
      3972
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6S 20`, and by no earlier member of the cover. -/
theorem end6S_satisfies_7 :
    Satisfies (Magma.end6S 20) [
      1441
    ] := by decide!
