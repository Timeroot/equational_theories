import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate sources: `Magma.srch10R803` (part 1 of 5)

For each of the `5` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `31` equations worth using as the *source* `L'` of a
`Magma.srch10R803` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `21` equations satisfied by `Magma.srch10R803 vsrch10R8030`, and by no earlier exhibit. -/
theorem srch10R803_satisfies_0 :
    Satisfies (Magma.srch10R803 vsrch10R8030) [
      3260, 3273, 3292, 3295, 3463, 3476, 3498, 3670, 3681, 3695, 3707, 3883, 3899, 3911, 4077,
      4086, 4102, 4114, 4413, 4415, 4430
    ] := by rw [esrch10R8030]; decide!
