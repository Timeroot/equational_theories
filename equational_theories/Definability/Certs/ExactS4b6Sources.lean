import equational_theories.Definability.ExactAut6S4b6

/-!
# Structural certificate sources: `Magma.exactS4b6`

For each of the following magmas, drawn from the `8` magmas on `Fin 6` whose automorphism group is
exactly the order-`24` group of `Magma.permES4b6`, the equations it satisfies that no earlier listed
magma does. Together they are the `35` equations that are worth using as the *source* `L'` of a
`Magma.exactS4b6` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrS4b6`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `17` equations satisfied by `Magma.exactS4b6 0`, and by no earlier member of the cover. -/
theorem exactS4b6_satisfies_0 :
    Satisfies (Magma.exactS4b6 0) [
      55, 102, 419, 436, 642, 826, 845, 1231, 1434, 1654, 1840, 2241, 2263, 2449, 3079, 3261, 3724
    ] := by decide!

/-- `10` equations satisfied by `Magma.exactS4b6 2`, and by no earlier member of the cover. -/
theorem exactS4b6_satisfies_1 :
    Satisfies (Magma.exactS4b6 2) [
      263, 513, 1312, 2060, 2327, 2672, 2875, 3058, 3749, 4073
    ] := by decide!

/-- `4` equations satisfied by `Magma.exactS4b6 4`, and by no earlier member of the cover. -/
theorem exactS4b6_satisfies_2 :
    Satisfies (Magma.exactS4b6 4) [
      127, 179, 1325, 2137
    ] := by decide!

/-- `4` equations satisfied by `Magma.exactS4b6 6`, and by no earlier member of the cover. -/
theorem exactS4b6_satisfies_3 :
    Satisfies (Magma.exactS4b6 6) [
      160, 212, 1455, 2267
    ] := by decide!
