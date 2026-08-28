import equational_theories.Definability.Srch_S10R300

/-!
# Structural certificate sources: `Magma.srch10R300` (part 2 of 7)

For each of the `7` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `133` equations worth using as the *source* `L'` of a
`Magma.srch10R300` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R300_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `13` equations satisfied by `Magma.srch10R300 vsrch10R3001`, and by no earlier exhibit. -/
theorem srch10R300_satisfies_1 :
    Satisfies (Magma.srch10R300 vsrch10R3001) [
      111, 434, 840, 1042, 1056, 1060, 1068, 1243, 1245, 1265, 1271, 1855, 1863
    ] := by rw [esrch10R3001]; decide!
