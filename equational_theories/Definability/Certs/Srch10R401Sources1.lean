import equational_theories.Definability.Srch_S10R401

/-!
# Structural certificate sources: `Magma.srch10R401` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `33` equations worth using as the *source* `L'` of a
`Magma.srch10R401` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R401_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `7` equations satisfied by `Magma.srch10R401 vsrch10R4011`, and by no earlier exhibit. -/
theorem srch10R401_satisfies_1 :
    Satisfies (Magma.srch10R401 vsrch10R4011) [
      455, 3214, 3297, 3489, 3703, 3895, 4109
    ] := by rw [esrch10R4011]; decide!
