import equational_theories.Definability.ExactAut7S4b7

/-!
# Structural certificate sources: `Magma.exactS4b7`

For each of the following magmas, drawn from the `160` magmas on `Fin 7` whose automorphism group is
exactly the order-`24` group of `Magma.permES4b7`, the equations it satisfies that no earlier listed
magma does. Together they are the `31` equations that are worth using as the *source* `L'` of a
`Magma.exactS4b7` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrS4b7`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `11` equations satisfied by `Magma.exactS4b7 74`, and by no earlier member of the cover. -/
theorem exactS4b7_satisfies_0 :
    Satisfies (Magma.exactS4b7 74) [
      1722, 1726, 2068, 2688, 2737, 2741, 2880, 3143, 3147, 4477, 4612
    ] := by decide!

/-- `11` equations satisfied by `Magma.exactS4b7 76`, and by no earlier member of the cover. -/
theorem exactS4b7_satisfies_1 :
    Satisfies (Magma.exactS4b7 76) [
      504, 508, 731, 910, 914, 981, 1543, 1925, 1929, 4297, 4424
    ] := by decide!

/-- `9` equations satisfied by `Magma.exactS4b7 72`, and by no earlier member of the cover. -/
theorem exactS4b7_satisfies_2 :
    Satisfies (Magma.exactS4b7 72) [
      3294, 3350, 3497, 3558, 3573, 3903, 3979, 4106, 4229
    ] := by decide!
