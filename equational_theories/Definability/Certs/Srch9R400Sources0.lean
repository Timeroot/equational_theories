import equational_theories.Definability.Srch_S9R400

/-!
# Structural certificate sources: `Magma.srch9R400` (part 1 of 3)

For each of the `3` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `5` equations worth using as the *source* `L'` of a
`Magma.srch9R400` certificate.

This file is generated; see the module docstring of `Definability.Srch_S9R400_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `2` equations satisfied by `Magma.srch9R400 vsrch9R4000`, and by no earlier exhibit. -/
theorem srch9R400_satisfies_0 :
    Satisfies (Magma.srch9R400 vsrch9R4000) [
      433, 854
    ] := by decide!
