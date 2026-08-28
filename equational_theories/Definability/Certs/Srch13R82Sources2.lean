import equational_theories.Definability.Srch_S13R82

/-!
# Structural certificate sources: `Magma.srch13R82` (part 3 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `27` equations worth using as the *source* `L'` of a
`Magma.srch13R82` certificate.

This file is generated; see the module docstring of `Definability.Srch_S13R82_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `7` equations satisfied by `Magma.srch13R82 vsrch13R822`, and by no earlier exhibit. -/
theorem srch13R82_satisfies_2 :
    Satisfies (Magma.srch13R82 vsrch13R822) [
      65, 679, 872, 907, 1491, 1518, 2264
    ] := by rw [esrch13R822]; decide!
