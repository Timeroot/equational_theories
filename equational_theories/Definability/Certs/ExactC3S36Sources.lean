import equational_theories.Definability.ExactAut6C3S36

/-!
# Structural certificate sources: `Magma.exactC3S36`

For each of the following magmas, drawn from the `156` magmas on `Fin 6` whose automorphism group is
exactly the order-`18` group of `Magma.permEC3S36`, the equations it satisfies that no earlier
listed magma does. Together they are the `49` equations that are worth using as the *source* `L'` of
a `Magma.exactC3S36` certificate -- the rest have such a model too, but the resulting facts are
already implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrC3S36`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `23` equations satisfied by `Magma.exactC3S36 21`, and by no earlier member of the cover. -/
theorem exactC3S36_satisfies_0 :
    Satisfies (Magma.exactC3S36 21) [
      103, 824, 827, 830, 831, 1027, 1030, 1033, 1034, 1233, 1235, 1236, 1237, 1633, 3059, 3069,
      3076, 3716, 3723, 3930, 4074, 4507, 4510
    ] := by decide!

/-- `22` equations satisfied by `Magma.exactC3S36 17`, and by no earlier member of the cover. -/
theorem exactC3S36_satisfies_1 :
    Satisfies (Magma.exactC3S36 17) [
      238, 476, 503, 1958, 2347, 2381, 2398, 2415, 2513, 2550, 2601, 2618, 2716, 2753, 2804,
      2821, 3281, 3566, 3790, 3803, 4456, 4490
    ] := by decide!

/-- `3` equations satisfied by `Magma.exactC3S36 26`, and by no earlier member of the cover. -/
theorem exactC3S36_satisfies_2 :
    Satisfies (Magma.exactC3S36 26) [
      156, 3097, 3732
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3S36 12`, and by no earlier member of the cover. -/
theorem exactC3S36_satisfies_3 :
    Satisfies (Magma.exactC3S36 12) [
      3728
    ] := by decide!
