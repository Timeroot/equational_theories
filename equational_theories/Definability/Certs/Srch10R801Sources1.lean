import equational_theories.Definability.Srch_S10R801

/-!
# Structural certificate sources: `Magma.srch10R801` (part 2 of 12)

For each of the `12` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `68` equations worth using as the *source* `L'` of a
`Magma.srch10R801` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R801_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `23` equations satisfied by `Magma.srch10R801 vsrch10R8011`, and by no earlier exhibit. -/
theorem srch10R801_satisfies_1 :
    Satisfies (Magma.srch10R801 vsrch10R8011) [
      343, 370, 3363, 3380, 3397, 3431, 3503, 3837, 3909, 4112, 4300, 4330, 4374, 4391, 4502,
      4593, 4625, 4638, 4649, 4663, 4669, 4682, 4693
    ] := by decide!
