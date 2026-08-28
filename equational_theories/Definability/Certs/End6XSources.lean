import equational_theories.Definability.ExactEnd6X

/-!
# Term-structural certificate sources: `Magma.end6X`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`28` monoid of `Magma.endE6X`, the equations it satisfies that no earlier listed
magma does. Together they are the `18` equations that are worth using as the *source* `L'` of a
`Magma.end6X` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `9` equations satisfied by `Magma.end6X 0`, and by no earlier member of the cover. -/
theorem end6X_satisfies_0 :
    Satisfies (Magma.end6X 0) [
      49, 416, 617, 618, 619, 621, 625, 1838, 3320
    ] := by decide!

/-- `9` equations satisfied by `Magma.end6X 1`, and by no earlier member of the cover. -/
theorem end6X_satisfies_1 :
    Satisfies (Magma.end6X 1) [
      260, 1691, 2852, 2882, 2919, 2936, 2973, 3055, 4192
    ] := by decide!
