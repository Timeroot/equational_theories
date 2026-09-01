import equational_theories.Definability.Srch_SR12

/-!
# Structural certificate sources: `Magma.srchR12` (part 1 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `4` equations worth using as the *source* `L'` of a
`Magma.srchR12` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR12_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.srchR12 vsrchR120`, and by no earlier exhibit. -/
theorem srchR12_satisfies_0 :
    Satisfies (Magma.srchR12 vsrchR120) [
      3919, 4400
    ] := by decide!
