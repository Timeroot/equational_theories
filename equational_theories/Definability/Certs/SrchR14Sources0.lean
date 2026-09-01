import equational_theories.Definability.Srch_SR14

/-!
# Structural certificate sources: `Magma.srchR14` (part 1 of 8)

For each of the `8` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `24` equations worth using as the *source* `L'` of a
`Magma.srchR14` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR14_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `6` equations satisfied by `Magma.srchR14 vsrchR140`, and by no earlier exhibit. -/
theorem srchR14_satisfies_0 :
    Satisfies (Magma.srchR14 vsrchR140) [
      1445, 1446, 1448, 1858, 1868, 1869
    ] := by decide!
