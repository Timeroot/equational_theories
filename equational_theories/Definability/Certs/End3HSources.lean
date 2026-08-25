import equational_theories.Definability.ExactEnd3H

/-!
# Term-structural certificate sources: `Magma.end3H`

For each of the following magmas, drawn from the `5` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`3` monoid of `Magma.endE3H`, the equations it satisfies that no earlier listed
magma does. Together they are the `46` equations that are worth using as the *source* `L'` of a
`Magma.end3H` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `24` equations satisfied by `Magma.end3H 2`, and by no earlier member of the cover. -/
theorem end3H_satisfies_0 :
    Satisfies (Magma.end3H 2) [
      3385, 3388, 3398, 3404, 3591, 3617, 3737, 3740, 3770, 3791, 3794, 3804, 3810, 3932, 3940,
      4143, 4176, 4197, 4210, 4364, 4515, 4525, 4541, 4679
    ] := by decide!

/-- `11` equations satisfied by `Magma.end3H 3`, and by no earlier member of the cover. -/
theorem end3H_satisfies_1 :
    Satisfies (Magma.end3H 3) [
      452, 455, 643, 647, 655, 658, 861, 1053, 1061, 1264, 1267
    ] := by decide!

/-- `11` equations satisfied by `Magma.end3H 4`, and by no earlier member of the cover. -/
theorem end3H_satisfies_2 :
    Satisfies (Magma.end3H 4) [
      2389, 2402, 2558, 2592, 2808, 2949, 2964, 2998, 3011, 3201, 3214
    ] := by decide!
