import equational_theories.Definability.Srch_S8R201

/-!
# Structural certificate sources: `Magma.srch8R201` (part 3 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `284` equations worth using as the *source* `L'` of a
`Magma.srch8R201` certificate.

This file is generated; see the module docstring of `Definability.Srch_S8R201_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `21` equations satisfied by `Magma.srch8R201 vsrch8R2012`, and by no earlier exhibit. -/
theorem srch8R201_satisfies_2 :
    Satisfies (Magma.srch8R201 vsrch8R2012) [
      58, 422, 442, 446, 450, 454, 458, 649, 653, 657, 661, 828, 848, 860, 864, 1437, 1668, 1875,
      3264, 3529, 3728
    ] := by rw [esrch8R2012]; decide!
