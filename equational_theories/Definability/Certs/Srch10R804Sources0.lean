import equational_theories.Definability.Srch_S10R804

/-!
# Structural certificate sources: `Magma.srch10R804` (part 1 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `26` equations worth using as the *source* `L'` of a
`Magma.srch10R804` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R804_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `13` equations satisfied by `Magma.srch10R804 vsrch10R8040`, and by no earlier exhibit. -/
theorem srch10R804_satisfies_0 :
    Satisfies (Magma.srch10R804 vsrch10R8040) [
      106, 839, 840, 841, 1037, 1245, 1246, 1247, 1260, 1261, 1636, 3726, 3727
    ] := by rw [esrch10R8040]; decide!
