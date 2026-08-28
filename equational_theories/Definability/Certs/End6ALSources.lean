import equational_theories.Definability.ExactEnd6AL

/-!
# Term-structural certificate sources: `Magma.end6AL`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`42` monoid of `Magma.endE6AL`, the equations it satisfies that no earlier listed
magma does. Together they are the `2` equations that are worth using as the *source* `L'` of a
`Magma.end6AL` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.end6AL 0`, and by no earlier member of the cover. -/
theorem end6AL_satisfies_0 :
    Satisfies (Magma.end6AL 0) [
      1041
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AL 1`, and by no earlier member of the cover. -/
theorem end6AL_satisfies_1 :
    Satisfies (Magma.end6AL 1) [
      2462
    ] := by decide!
