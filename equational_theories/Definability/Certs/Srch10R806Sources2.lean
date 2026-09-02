import equational_theories.Definability.Srch_S10R806

/-!
# Structural certificate sources: `Magma.srch10R806` (part 3 of 6)

For each of the `6` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `12` equations worth using as the *source* `L'` of a
`Magma.srch10R806` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R806_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `2` equations satisfied by `Magma.srch10R806 vsrch10R8062`, and by no earlier exhibit. -/
theorem srch10R806_satisfies_2 :
    Satisfies (Magma.srch10R806 vsrch10R8062) [
      2493, 2899
    ] := by rw [esrch10R8062]; decide!
