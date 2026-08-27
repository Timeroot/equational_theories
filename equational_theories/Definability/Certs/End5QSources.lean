import equational_theories.Definability.ExactEnd5Q

/-!
# Term-structural certificate sources: `Magma.end5Q`

For each of the following magmas, drawn from the `2` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`17` monoid of `Magma.endE5Q`, the equations it satisfies that no earlier listed
magma does. Together they are the `8` equations that are worth using as the *source* `L'` of a
`Magma.end5Q` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `4` equations satisfied by `Magma.end5Q 0`, and by no earlier member of the cover. -/
theorem end5Q_satisfies_0 :
    Satisfies (Magma.end5Q 0) [
      434, 837, 840, 1855
    ] := by decide!

/-- `4` equations satisfied by `Magma.end5Q 1`, and by no earlier member of the cover. -/
theorem end5Q_satisfies_1 :
    Satisfies (Magma.end5Q 1) [
      1724, 2739, 2778, 3145
    ] := by decide!
