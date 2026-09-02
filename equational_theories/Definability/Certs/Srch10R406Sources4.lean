import equational_theories.Definability.Srch_S10R406

/-!
# Structural certificate sources: `Magma.srch10R406` (part 5 of 6)

For each of the `6` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `163` equations worth using as the *source* `L'` of a
`Magma.srch10R406` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R406_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `2` equations satisfied by `Magma.srch10R406 vsrch10R4064`, and by no earlier exhibit. -/
theorem srch10R406_satisfies_4 :
    Satisfies (Magma.srch10R406 vsrch10R4064) [
      3317, 3321
    ] := by rw [esrch10R4064]; decide!
