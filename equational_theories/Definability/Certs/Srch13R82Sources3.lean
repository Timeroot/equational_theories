import equational_theories.Definability.Srch_S13R82

/-!
# Structural certificate sources: `Magma.srch13R82` (part 4 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `27` equations worth using as the *source* `L'` of a
`Magma.srch13R82` certificate.

This file is generated; see the module docstring of `Definability.Srch_S13R82_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `3` equations satisfied by `Magma.srch13R82 vsrch13R823`, and by no earlier exhibit. -/
theorem srch13R82_satisfies_3 :
    Satisfies (Magma.srch13R82 vsrch13R823) [
      4321, 4443, 4636
    ] := by rw [esrch13R823]; decide!
