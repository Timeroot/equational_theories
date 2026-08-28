import equational_theories.Definability.Srch_S8R201

/-!
# Structural certificate sources: `Magma.srch8R201` (part 2 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `284` equations worth using as the *source* `L'` of a
`Magma.srch8R201` certificate.

This file is generated; see the module docstring of `Definability.Srch_S8R201_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `22` equations satisfied by `Magma.srch8R201 vsrch8R2011`, and by no earlier exhibit. -/
theorem srch8R201_satisfies_1 :
    Satisfies (Magma.srch8R201 vsrch8R2011) [
      325, 377, 3315, 3318, 3518, 3521, 3714, 3721, 3724, 3924, 3927, 4120, 4127, 4283, 4314,
      4398, 4433, 4436, 4472, 4512, 4598, 4629
    ] := by rw [esrch8R2011]; decide!
