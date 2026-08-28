import equational_theories.Definability.ExactEnd6AN

/-!
# Term-structural certificate sources: `Magma.end6AN`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`24` monoid of `Magma.endE6AN`, the equations it satisfies that no earlier listed
magma does. Together they are the `4` equations that are worth using as the *source* `L'` of a
`Magma.end6AN` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `2` equations satisfied by `Magma.end6AN 0`, and by no earlier member of the cover. -/
theorem end6AN_satisfies_0 :
    Satisfies (Magma.end6AN 0) [
      2244, 2670
    ] := by decide!

/-- `2` equations satisfied by `Magma.end6AN 2`, and by no earlier member of the cover. -/
theorem end6AN_satisfies_1 :
    Satisfies (Magma.end6AN 2) [
      882, 1285
    ] := by decide!
