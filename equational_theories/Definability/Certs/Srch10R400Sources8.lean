import equational_theories.Definability.Srch_S10R400

/-!
# Structural certificate sources: `Magma.srch10R400` (part 9 of 10)

For each of the `9` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `202` equations worth using as the *source* `L'` of a
`Magma.srch10R400` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R400_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `1` equations satisfied by `Magma.srch10R400 vsrch10R4007`, and by no earlier exhibit. -/
theorem srch10R400_satisfies_7 :
    Satisfies (Magma.srch10R400 vsrch10R4007) [
      3601
    ] := by rw [esrch10R4007]; decide!
