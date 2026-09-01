import equational_theories.Definability.Srch_SR7

/-!
# Structural certificate sources: `Magma.srchR7` (part 1 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `14` equations worth using as the *source* `L'` of a
`Magma.srchR7` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR7_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `5` equations satisfied by `Magma.srchR7 vsrchR70`, and by no earlier exhibit. -/
theorem srchR7_satisfies_0 :
    Satisfies (Magma.srchR7 vsrchR70) [
      839, 1239, 1245, 1259, 1260
    ] := by decide!
