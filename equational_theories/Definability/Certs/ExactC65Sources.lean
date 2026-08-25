import equational_theories.Definability.ExactAut5C65

/-!
# Structural certificate sources: `Magma.exactC65`

For each of the following magmas, drawn from the `2592` magmas on `Fin 5` whose automorphism group
is exactly the order-`6` group of `Magma.permEC65`, the equations it satisfies that no earlier
listed magma does. Together they are the `50` equations that are worth using as the *source* `L'` of
a `Magma.exactC65` certificate -- the rest have such a model too, but the resulting facts are
already implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrC65`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `19` equations satisfied by `Magma.exactC65 20`, and by no earlier member of the cover. -/
theorem exactC65_satisfies_0 :
    Satisfies (Magma.exactC65 20) [
      103, 827, 830, 831, 1030, 1033, 1034, 1235, 1237, 1633, 3059, 3069, 3076, 3716, 3723, 3930,
      4074, 4507, 4510
    ] := by decide!

/-- `18` equations satisfied by `Magma.exactC65 513`, and by no earlier member of the cover. -/
theorem exactC65_satisfies_1 :
    Satisfies (Magma.exactC65 513) [
      238, 476, 503, 1958, 2381, 2415, 2550, 2601, 2618, 2716, 2753, 2804, 2821, 3566, 3790,
      3803, 4456, 4490
    ] := by decide!

/-- `7` equations satisfied by `Magma.exactC65 48`, and by no earlier member of the cover. -/
theorem exactC65_satisfies_2 :
    Satisfies (Magma.exactC65 48) [
      153, 442, 446, 450, 454, 458, 3728
    ] := by decide!

/-- `6` equations satisfied by `Magma.exactC65 484`, and by no earlier member of the cover. -/
theorem exactC65_satisfies_3 :
    Satisfies (Magma.exactC65 484) [
      3061, 3081, 3089, 3093, 3097, 3732
    ] := by decide!
