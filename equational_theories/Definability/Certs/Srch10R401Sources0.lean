import equational_theories.Definability.Srch_S10R401

/-!
# Structural certificate sources: `Magma.srch10R401` (part 1 of 2)

For each of the `2` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `33` equations worth using as the *source* `L'` of a
`Magma.srch10R401` certificate.

This file is generated; see the module docstring of `Definability.Srch_S10R401_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- `26` equations satisfied by `Magma.srch10R401 vsrch10R4010`, and by no earlier exhibit. -/
theorem srch10R401_satisfies_0 :
    Satisfies (Magma.srch10R401 vsrch10R4010) [
      481, 695, 887, 978, 1101, 1384, 1488, 1496, 1537, 1710, 1740, 1902, 1993, 2041, 2105, 2146,
      2319, 2602, 2725, 2755, 3008, 3161, 4325, 4461, 4491, 4620
    ] := by rw [esrch10R4010]; decide!
