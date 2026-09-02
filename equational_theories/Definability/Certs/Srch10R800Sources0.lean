import equational_theories.Definability.Srch_S10R800

/-!
# Structural certificate sources: `Magma.srch10R800` (part 1 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `4` equations worth using as the *source* `L'` of a
`Magma.srch10R800` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R800_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `2` equations satisfied by `Magma.srch10R800 vsrch10R8000`, and by no earlier exhibit. -/
theorem srch10R800_satisfies_0 :
    Satisfies (Magma.srch10R800 vsrch10R8000) [
      1705, 2169
    ] := by decide!
