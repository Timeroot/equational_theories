import equational_theories.Definability.ExactEnd5S

/-!
# Term-structural certificate sources: `Magma.end5S`

For each of the following magmas, drawn from the `16` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`109` monoid of `Magma.endE5S`, the equations it satisfies that no earlier listed
magma does. Together they are the `30` equations that are worth using as the *source* `L'` of a
`Magma.end5S` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `10` equations satisfied by `Magma.end5S 2`, and by no earlier member of the cover. -/
theorem end5S_satisfies_0 :
    Satisfies (Magma.end5S 2) [
      3677, 3680, 3718, 3755, 3790, 3794, 3798, 4525, 4542, 4559
    ] := by decide!

/-- `10` equations satisfied by `Magma.end5S 9`, and by no earlier member of the cover. -/
theorem end5S_satisfies_1 :
    Satisfies (Magma.end5S 9) [
      3665, 3666, 3716, 3735, 3736, 3737, 3738, 4439, 4515, 4519
    ] := by decide!

/-- `4` equations satisfied by `Magma.end5S 5`, and by no earlier member of the cover. -/
theorem end5S_satisfies_2 :
    Satisfies (Magma.end5S 5) [
      835, 1488, 1887, 2706
    ] := by decide!

/-- `4` equations satisfied by `Magma.end5S 14`, and by no earlier member of the cover. -/
theorem end5S_satisfies_3 :
    Satisfies (Magma.end5S 14) [
      823, 1645, 2041, 2662
    ] := by decide!

/-- `1` equations satisfied by `Magma.end5S 1`, and by no earlier member of the cover. -/
theorem end5S_satisfies_4 :
    Satisfies (Magma.end5S 1) [
      838
    ] := by decide!

/-- `1` equations satisfied by `Magma.end5S 12`, and by no earlier member of the cover. -/
theorem end5S_satisfies_5 :
    Satisfies (Magma.end5S 12) [
      2665
    ] := by decide!
