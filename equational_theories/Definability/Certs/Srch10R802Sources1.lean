import equational_theories.Definability.Srch_S10R802

/-!
# Structural certificate sources: `Magma.srch10R802` (part 2 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `34` equations worth using as the *source* `L'` of a
`Magma.srch10R802` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R802_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `17` equations satisfied by `Magma.srch10R802 vsrch10R8021`, and by no earlier exhibit. -/
theorem srch10R802_satisfies_1 :
    Satisfies (Magma.srch10R802 vsrch10R8021) [
      395, 727, 964, 1594, 3566, 3790, 3972, 3989, 4006, 4023, 4040, 4243, 4456, 4490, 4615,
      4645, 4689
    ] := by decide!
