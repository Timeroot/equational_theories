import equational_theories.Definability.Srch_S9R410

/-!
# Structural certificate sources: `Magma.srch9R410`

For each of the `1` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `8` equations worth using as the *source* `L'` of a
`Magma.srch9R410` certificate.

This file is generated; see the module docstring of `Definability.Srch_S9R410_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `8` equations satisfied by `Magma.srch9R410 vsrch9R4100`, and by no earlier exhibit. -/
theorem srch9R410_satisfies_0 :
    Satisfies (Magma.srch9R410 vsrch9R4100) [
      4301, 4311, 4430, 4449, 4454, 4466, 4646, 4652
    ] := by rw [esrch9R4100]; decide!
