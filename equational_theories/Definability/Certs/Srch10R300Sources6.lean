import equational_theories.Definability.Srch_S10R300

/-!
# Structural certificate sources: `Magma.srch10R300` (part 7 of 7)

For each of the `7` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `133` equations worth using as the *source* `L'` of a
`Magma.srch10R300` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R300_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.srch10R300 vsrch10R3006`, and by no earlier exhibit. -/
theorem srch10R300_satisfies_6 :
    Satisfies (Magma.srch10R300 vsrch10R3006) [
      2712, 3180
    ] := by rw [esrch10R3006]; decide!
