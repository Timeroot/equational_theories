import equational_theories.Definability.ExactAut6C2A4b6

/-!
# Structural certificate sources: `Magma.exactC2A4b6`

For each of the following magmas, drawn from the `72` magmas on `Fin 6` whose automorphism group is
exactly the order-`24` group of `Magma.permEC2A4b6`, the equations it satisfies that no earlier
listed magma does. Together they are the `2` equations that are worth using as the *source* `L'` of
a `Magma.exactC2A4b6` certificate -- the rest have such a model too, but the resulting facts are
already implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrC2A4b6`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.exactC2A4b6 25`, and by no earlier member of the cover. -/
theorem exactC2A4b6_satisfies_0 :
    Satisfies (Magma.exactC2A4b6 25) [
      510, 3281
    ] := by decide!
