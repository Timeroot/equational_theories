import equational_theories.Definability.ExactAut5D65

/-!
# Structural certificate sources: `Magma.exactD65`

For each of the following magmas, drawn from the `106` magmas on `Fin 5` whose automorphism group is
exactly the order-`12` group of `Magma.permED65`, the equations it satisfies that no earlier listed
magma does. Together they are the `3` equations that are worth using as the *source* `L'` of a
`Magma.exactD65` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrD65`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.exactD65 74`, and by no earlier member of the cover. -/
theorem exactD65_satisfies_0 :
    Satisfies (Magma.exactD65 74) [
      2670, 2853
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactD65 83`, and by no earlier member of the cover. -/
theorem exactD65_satisfies_1 :
    Satisfies (Magma.exactD65 83) [
      676
    ] := by decide!
