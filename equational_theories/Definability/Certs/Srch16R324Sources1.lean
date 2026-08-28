import equational_theories.Definability.Srch_S16R324

/-!
# Structural certificate sources: `Magma.srch16R324` (part 2 of 3)

For each of the `3` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `24` equations worth using as the *source* `L'` of a
`Magma.srch16R324` certificate.

This file is generated; see the module docstring of `Definability.Srch_S16R324_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.srch16R324 vsrch16R3241`, and by no earlier exhibit. -/
theorem srch16R324_satisfies_1 :
    Satisfies (Magma.srch16R324 vsrch16R3241) [
      474, 677, 1076, 1289, 2294, 2507, 2913, 3116
    ] := by rw [esrch16R3241]; decide!
