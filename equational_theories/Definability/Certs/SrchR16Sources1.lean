import equational_theories.Definability.Srch_SR16

/-!
# Structural certificate sources: `Magma.srchR16` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `3` equations worth using as the *source* `L'` of a
`Magma.srchR16` certificate.

This file is generated; see the module docstring of `Definability.Srch_SR16_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.srchR16 vsrchR161`, and by no earlier exhibit. -/
theorem srchR16_satisfies_1 :
    Satisfies (Magma.srchR16 vsrchR161) [
      690
    ] := by decide!
