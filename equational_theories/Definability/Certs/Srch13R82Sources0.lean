import equational_theories.Definability.Srch_S13R82

/-!
# Structural certificate sources: `Magma.srch13R82` (part 1 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `27` equations worth using as the *source* `L'` of a
`Magma.srch13R82` certificate.

This file is generated; see the module docstring of `Definability.Srch_S13R82_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `10` equations satisfied by `Magma.srch13R82 vsrch13R820`, and by no earlier exhibit. -/
theorem srch13R82_satisfies_0 :
    Satisfies (Magma.srch13R82 vsrch13R820) [
      501, 1076, 1083, 1286, 1313, 2294, 2301, 2504, 2531, 3106
    ] := by rw [esrch13R820]; decide!
