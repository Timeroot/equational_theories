import equational_theories.Definability.Srch_S13R82

/-!
# Structural certificate sources: `Magma.srch13R82` (part 2 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `27` equations worth using as the *source* `L'` of a
`Magma.srch13R82` certificate.

This file is generated; see the module docstring of `Definability.Srch_S13R82_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `7` equations satisfied by `Magma.srch13R82 vsrch13R821`, and by no earlier exhibit. -/
theorem srch13R82_satisfies_1 :
    Satisfies (Magma.srch13R82 vsrch13R821) [
      261, 1288, 2054, 2061, 2660, 2700, 2873
    ] := by rw [esrch13R821]; decide!
