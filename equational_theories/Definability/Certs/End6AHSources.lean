import equational_theories.Definability.ExactEnd6AH

/-!
# Term-structural certificate sources: `Magma.end6AH`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`28` monoid of `Magma.endE6AH`, the equations it satisfies that no earlier listed
magma does. Together they are the `2` equations that are worth using as the *source* `L'` of a
`Magma.end6AH` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.end6AH 0`, and by no earlier member of the cover. -/
theorem end6AH_satisfies_0 :
    Satisfies (Magma.end6AH 0) [
      2270
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AH 2`, and by no earlier member of the cover. -/
theorem end6AH_satisfies_1 :
    Satisfies (Magma.end6AH 2) [
      2203
    ] := by decide!
