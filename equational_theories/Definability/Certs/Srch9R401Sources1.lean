import equational_theories.Definability.Srch_S9R401

/-!
# Structural certificate sources: `Magma.srch9R401` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `10` equations worth using as the *source* `L'` of a
`Magma.srch9R401` certificate.

This file is generated; see the module docstring of `Definability.Srch_S9R401_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `5` equations satisfied by `Magma.srch9R401 vsrch9R4011`, and by no earlier exhibit. -/
theorem srch9R401_satisfies_1 :
    Satisfies (Magma.srch9R401 vsrch9R4011) [
      65, 679, 872, 1491, 1518
    ] := by decide!
