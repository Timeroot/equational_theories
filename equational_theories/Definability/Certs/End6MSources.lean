import equational_theories.Definability.ExactEnd6M

/-!
# Term-structural certificate sources: `Magma.end6M`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`141` monoid of `Magma.endE6M`, the equations it satisfies that no earlier listed
magma does. Together they are the `30` equations that are worth using as the *source* `L'` of a
`Magma.end6M` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `15` equations satisfied by `Magma.end6M 0`, and by no earlier member of the cover. -/
theorem end6M_satisfies_0 :
    Satisfies (Magma.end6M 0) [
      1834, 1835, 1847, 1851, 1853, 1855, 1857, 1861, 1863, 1865, 3315, 3318, 3321, 3322, 3323
    ] := by decide!

/-- `15` equations satisfied by `Magma.end6M 1`, and by no earlier member of the cover. -/
theorem end6M_satisfies_1 :
    Satisfies (Magma.end6M 1) [
      1631, 1637, 1644, 1650, 1672, 1718, 1721, 1724, 1731, 1746, 4118, 4138, 4165, 4175, 4226
    ] := by decide!
