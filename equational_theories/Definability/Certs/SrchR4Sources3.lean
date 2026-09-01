import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate sources: `Magma.srchR4` (part 4 of 12)

For each of the `12` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `28` equations worth using as the *source* `L'` of a
`Magma.srchR4` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.srchR4 vsrchR43`, and by no earlier exhibit. -/
theorem srchR4_satisfies_3 :
    Satisfies (Magma.srchR4 vsrchR43) [
      3698, 4460
    ] := by decide!
