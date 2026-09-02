import equational_theories.Definability.Srch_S10R804

/-!
# Structural certificate sources: `Magma.srch10R804` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `26` equations worth using as the *source* `L'` of a
`Magma.srch10R804` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R804_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `13` equations satisfied by `Magma.srch10R804 vsrch10R8041`, and by no earlier exhibit. -/
theorem srch10R804_satisfies_1 :
    Satisfies (Magma.srch10R804 vsrch10R8041) [
      224, 1904, 2306, 2322, 2333, 2368, 2376, 2499, 2739, 2774, 2782, 3769, 3786
    ] := by rw [esrch10R8041]; decide!
