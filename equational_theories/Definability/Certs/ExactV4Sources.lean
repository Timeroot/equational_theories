import equational_theories.Definability.ExactAut4V4

/-!
# Structural certificate sources: `Magma.exactV4`

For each of the following magmas, drawn from the `240` magmas on `Fin 4` whose automorphism group is
exactly the order-`4` group of `Magma.permEV4`, the equations it satisfies that no earlier listed
magma does. Together they are the `8` equations that are worth using as the *source* `L'` of a
`Magma.exactV4` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut4`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrV4`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `5` equations satisfied by `Magma.exactV4 0`, and by no earlier member of the cover. -/
theorem exactV4_satisfies_0 :
    Satisfies (Magma.exactV4 0) [
      3724, 3917, 4398, 4436, 4512
    ] := by decide!

/-- `3` equations satisfied by `Magma.exactV4 16`, and by no earlier member of the cover. -/
theorem exactV4_satisfies_1 :
    Satisfies (Magma.exactV4 16) [
      3749, 4406, 4442
    ] := by decide!
