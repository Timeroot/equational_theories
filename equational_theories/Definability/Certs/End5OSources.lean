import equational_theories.Definability.ExactEnd5O

/-!
# Term-structural certificate sources: `Magma.end5O`

For each of the following magmas, drawn from the `180` magmas on `Fin 5` whose endomorphism monoid
is exactly the order-`9` monoid of `Magma.endE5O`, the equations it satisfies that no earlier listed
magma does. Together they are the `21` equations that are worth using as the *source* `L'` of a
`Magma.end5O` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `6` equations satisfied by `Magma.end5O 37`, and by no earlier member of the cover. -/
theorem end5O_satisfies_0 :
    Satisfies (Magma.end5O 37) [
      1441, 1867, 3061, 3081, 3089, 3097
    ] := by decide!

/-- `6` equations satisfied by `Magma.end5O 89`, and by no earlier member of the cover. -/
theorem end5O_satisfies_1 :
    Satisfies (Magma.end5O 89) [
      1431, 1636, 1640, 1843, 1849, 3463
    ] := by decide!

/-- `5` equations satisfied by `Magma.end5O 120`, and by no earlier member of the cover. -/
theorem end5O_satisfies_2 :
    Satisfies (Magma.end5O 120) [
      1664, 1687, 1904, 2040, 3883
    ] := by decide!

/-- `2` equations satisfied by `Magma.end5O 20`, and by no earlier member of the cover. -/
theorem end5O_satisfies_3 :
    Satisfies (Magma.end5O 20) [
      458, 2037
    ] := by decide!

/-- `1` equations satisfied by `Magma.end5O 17`, and by no earlier member of the cover. -/
theorem end5O_satisfies_4 :
    Satisfies (Magma.end5O 17) [
      1437
    ] := by decide!

/-- `1` equations satisfied by `Magma.end5O 34`, and by no earlier member of the cover. -/
theorem end5O_satisfies_5 :
    Satisfies (Magma.end5O 34) [
      2070
    ] := by decide!
