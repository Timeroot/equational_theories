import equational_theories.Definability.Srch_SR9

/-!
# Structural certificate sources: `Magma.srchR9` (part 2 of 5)

For each of the `5` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `15` equations worth using as the *source* `L'` of a
`Magma.srchR9` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR9_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `4` equations satisfied by `Magma.srchR9 vsrchR91`, and by no earlier exhibit. -/
theorem srchR9_satisfies_1 :
    Satisfies (Magma.srchR9 vsrchR91) [
      3363, 3380, 3397, 3431
    ] := by decide!
