import equational_theories.Definability.Srch_S4R2

/-!
# Structural certificate sources: `Magma.srch4R2`

For each of the `1` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `4` equations worth using as the *source* `L'` of a
`Magma.srch4R2` certificate.

This file is generated; see the module docstring of `Definability.Srch_S4R2_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `4` equations satisfied by `Magma.srch4R2 vsrch4R20`, and by no earlier exhibit. -/
theorem srch4R2_satisfies_0 :
    Satisfies (Magma.srch4R2 vsrch4R20) [
      1483, 1485, 2162, 2163
    ] := by decide!
