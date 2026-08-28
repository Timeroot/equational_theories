import equational_theories.Definability.Srch_S16R324

/-!
# Structural certificate sources: `Magma.srch16R324` (part 1 of 3)

For each of the `3` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `24` equations worth using as the *source* `L'` of a
`Magma.srch16R324` certificate.

This file is generated; see the module docstring of `Definability.Srch_S16R324_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.srch16R324 vsrch16R3240`, and by no earlier exhibit. -/
theorem srch16R324_satisfies_0 :
    Satisfies (Magma.srch16R324 vsrch16R3240) [
      464, 670, 1083, 1286, 2301, 2504, 2937, 3103
    ] := by rw [esrch16R3240]; decide!
