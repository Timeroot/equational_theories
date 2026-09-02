import equational_theories.Definability.Srch_S9R1000

/-!
# Structural certificate sources: `Magma.srch9R1000` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `46` equations worth using as the *source* `L'` of a
`Magma.srch9R1000` certificate.

This file is generated; see the module docstring of `Definability.Srch_S9R1000_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `14` equations satisfied by `Magma.srch9R1000 vsrch9R10001`, and by no earlier exhibit. -/
theorem srch9R1000_satisfies_1 :
    Satisfies (Magma.srch9R1000 vsrch9R10001) [
      333, 385, 3346, 3546, 3752, 3759, 3952, 4155, 4165, 4291, 4406, 4445, 4480, 4606
    ] := by rw [esrch9R10001]; decide!
