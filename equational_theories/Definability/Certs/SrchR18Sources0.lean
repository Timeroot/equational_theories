import equational_theories.Definability.Srch_SR18

/-!
# Structural certificate sources: `Magma.srchR18` (part 1 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `2` equations worth using as the *source* `L'` of a
`Magma.srchR18` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR18_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.srchR18 vsrchR180`, and by no earlier exhibit. -/
theorem srchR18_satisfies_0 :
    Satisfies (Magma.srchR18 vsrchR180) [
      2045
    ] := by decide!
