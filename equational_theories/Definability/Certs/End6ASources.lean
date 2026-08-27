import equational_theories.Definability.ExactEnd6A

/-!
# Term-structural certificate sources: `Magma.end6A`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`36` monoid of `Magma.endE6A`, the equations it satisfies that no earlier listed
magma does. Together they are the `37` equations that are worth using as the *source* `L'` of a
`Magma.end6A` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `36` equations satisfied by `Magma.end6A 1`, and by no earlier member of the cover. -/
theorem end6A_satisfies_0 :
    Satisfies (Magma.end6A 1) [
      267, 268, 269, 2654, 2657, 2658, 2664, 2671, 2686, 2689, 2690, 2692, 2693, 2694, 2695,
      2848, 2851, 2859, 2861, 2864, 2867, 2869, 2870, 2874, 2877, 2879, 2881, 2884, 2885, 2889,
      2892, 2893, 2895, 2896, 2897, 2898
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6A 0`, and by no earlier member of the cover. -/
theorem end6A_satisfies_1 :
    Satisfies (Magma.end6A 0) [
      672
    ] := by decide!
