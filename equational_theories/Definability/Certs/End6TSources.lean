import equational_theories.Definability.ExactEnd6T

/-!
# Term-structural certificate sources: `Magma.end6T`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`28` monoid of `Magma.endE6T`, the equations it satisfies that no earlier listed
magma does. Together they are the `50` equations that are worth using as the *source* `L'` of a
`Magma.end6T` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `25` equations satisfied by `Magma.end6T 0`, and by no earlier member of the cover. -/
theorem end6T_satisfies_0 :
    Satisfies (Magma.end6T 0) [
      65, 117, 270, 513, 562, 679, 713, 872, 1085, 1112, 1238, 1315, 1353, 1491, 1518, 2100,
      2115, 2456, 2584, 2804, 2899, 2973, 3065, 3102, 3176
    ] := by decide!

/-- `25` equations satisfied by `Magma.end6T 2`, and by no earlier member of the cover. -/
theorem end6T_satisfies_1 :
    Satisfies (Magma.end6T 2) [
      48, 209, 261, 412, 413, 415, 615, 618, 827, 1022, 1032, 1453, 2054, 2061, 2240, 2254, 2257,
      2260, 2460, 2467, 2660, 2856, 2873, 3079, 3091
    ] := by decide!
