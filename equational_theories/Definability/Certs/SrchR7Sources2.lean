import equational_theories.Definability.Srch_SR7

/-!
# Structural certificate sources: `Magma.srchR7` (part 3 of 4)

For each of the `4` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `14` equations worth using as the *source* `L'` of a
`Magma.srchR7` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR7_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.srchR7 vsrchR72`, and by no earlier exhibit. -/
theorem srchR7_satisfies_2 :
    Satisfies (Magma.srchR7 vsrchR72) [
      3726, 4511
    ] := by decide!
