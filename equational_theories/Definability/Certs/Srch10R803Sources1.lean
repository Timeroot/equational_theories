import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate sources: `Magma.srch10R803` (part 2 of 5)

For each of the `5` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `31` equations worth using as the *source* `L'` of a
`Magma.srch10R803` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `3` equations satisfied by `Magma.srch10R803 vsrch10R8031`, and by no earlier exhibit. -/
theorem srch10R803_satisfies_1 :
    Satisfies (Magma.srch10R803 vsrch10R8031) [
      2592, 2998, 3201
    ] := by rw [esrch10R8031]; decide!
