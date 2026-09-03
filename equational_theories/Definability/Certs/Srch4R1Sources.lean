import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate sources: `Magma.srch4R1`

For each of the `1` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `8` equations worth using as the *source* `L'` of a
`Magma.srch4R1` certificate.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `8` equations satisfied by `Magma.srch4R1 vsrch4R10`, and by no earlier exhibit. -/
theorem srch4R1_satisfies_0 :
    Satisfies (Magma.srch4R1 vsrch4R10) [
      167, 168, 1480, 1486, 1487, 2089, 2126, 2164
    ] := by decide!
