import equational_theories.Definability.Srch_S8R201

/-!
# Structural certificate sources: `Magma.srch8R201` (part 4 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `284` equations worth using as the *source* `L'` of a
`Magma.srch8R201` certificate.

This file is generated; see the module docstring of `Definability.Srch_S8R201_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `21` equations satisfied by `Magma.srch8R201 vsrch8R2013`, and by no earlier exhibit. -/
theorem srch8R201_satisfies_3 :
    Satisfies (Magma.srch8R201 vsrch8R2013) [
      333, 385, 3346, 3353, 3546, 3556, 3749, 3752, 3759, 3952, 3962, 4155, 4165, 4291, 4320,
      4406, 4442, 4445, 4480, 4606, 4635
    ] := by rw [esrch8R2013]; decide!
