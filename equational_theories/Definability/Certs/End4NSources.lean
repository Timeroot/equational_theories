import equational_theories.Definability.ExactEnd4N

/-!
# Term-structural certificate sources: `Magma.end4N`

For each of the following magmas, drawn from the `194` magmas on `Fin 4` whose endomorphism monoid
is exactly the order-`7` monoid of `Magma.endE4N`, the equations it satisfies that no earlier listed
magma does. Together they are the `16` equations that are worth using as the *source* `L'` of a
`Magma.end4N` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `7` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `4` equations satisfied by `Magma.end4N 42`, and by no earlier member of the cover. -/
theorem end4N_satisfies_0 :
    Satisfies (Magma.end4N 42) [
      2306, 2330, 2699, 2774
    ] := by decide!

/-- `3` equations satisfied by `Magma.end4N 8`, and by no earlier member of the cover. -/
theorem end4N_satisfies_1 :
    Satisfies (Magma.end4N 8) [
      839, 1242, 1260
    ] := by decide!

/-- `3` equations satisfied by `Magma.end4N 58`, and by no earlier member of the cover. -/
theorem end4N_satisfies_2 :
    Satisfies (Magma.end4N 58) [
      167, 1682, 1885
    ] := by decide!

/-- `2` equations satisfied by `Magma.end4N 6`, and by no earlier member of the cover. -/
theorem end4N_satisfies_3 :
    Satisfies (Magma.end4N 6) [
      3317, 3321
    ] := by decide!

/-- `2` equations satisfied by `Magma.end4N 44`, and by no earlier member of the cover. -/
theorem end4N_satisfies_4 :
    Satisfies (Magma.end4N 44) [
      4175, 4209
    ] := by decide!

/-- `1` equations satisfied by `Magma.end4N 57`, and by no earlier member of the cover. -/
theorem end4N_satisfies_5 :
    Satisfies (Magma.end4N 57) [
      1085
    ] := by decide!

/-- `1` equations satisfied by `Magma.end4N 101`, and by no earlier member of the cover. -/
theorem end4N_satisfies_6 :
    Satisfies (Magma.end4N 101) [
      2467
    ] := by decide!
