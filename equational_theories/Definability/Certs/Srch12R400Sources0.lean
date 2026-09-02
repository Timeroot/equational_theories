import equational_theories.Definability.Srch_S12R400

/-!
# Structural certificate sources: `Magma.srch12R400` (part 1 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `2` equations worth using as the *source* `L'` of a
`Magma.srch12R400` certificate.

This file is generated; see the module docstring of `Definability.Srch_S12R400_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `1` equations satisfied by `Magma.srch12R400 vsrch12R4000`, and by no earlier exhibit. -/
theorem srch12R400_satisfies_0 :
    Satisfies (Magma.srch12R400 vsrch12R4000) [
      4424
    ] := by rw [esrch12R4000]; decide!
