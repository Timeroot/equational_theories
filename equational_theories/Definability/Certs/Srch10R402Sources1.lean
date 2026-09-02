import equational_theories.Definability.Srch_S10R402

/-!
# Structural certificate sources: `Magma.srch10R402` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `2` equations worth using as the *source* `L'` of a
`Magma.srch10R402` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R402_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `1` equations satisfied by `Magma.srch10R402 vsrch10R4021`, and by no earlier exhibit. -/
theorem srch10R402_satisfies_1 :
    Satisfies (Magma.srch10R402 vsrch10R4021) [
      882
    ] := by rw [esrch10R4021]; decide!
