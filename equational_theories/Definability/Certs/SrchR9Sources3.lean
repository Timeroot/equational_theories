import equational_theories.Definability.Srch_SR9

/-!
# Structural certificate sources: `Magma.srchR9` (part 4 of 5)

For each of the `5` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `15` equations worth using as the *source* `L'` of a
`Magma.srchR9` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR9_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.srchR9 vsrchR93`, and by no earlier exhibit. -/
theorem srchR9_satisfies_3 :
    Satisfies (Magma.srchR9 vsrchR93) [
      3476, 3498
    ] := by decide!
