import equational_theories.Definability.ExactEnd5M

/-!
# Term-structural certificate sources: `Magma.end5M`

For each of the following magmas, drawn from the `4` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`25` monoid of `Magma.endE5M`, the equations it satisfies that no earlier listed
magma does. Together they are the `64` equations that are worth using as the *source* `L'` of a
`Magma.end5M` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `36` equations satisfied by `Magma.end5M 2`, and by no earlier member of the cover. -/
theorem end5M_satisfies_0 :
    Satisfies (Magma.end5M 2) [
      257, 260, 270, 290, 616, 619, 1478, 2306, 2314, 2513, 2567, 2584, 2649, 2655, 2716, 2774,
      2778, 2849, 2852, 2862, 2882, 2919, 2956, 2973, 2990, 3024, 3102, 3108, 3122, 3149, 3159,
      3176, 3193, 3210, 3227, 3803
    ] := by decide!

/-- `28` equations satisfied by `Magma.end5M 0`, and by no earlier member of the cover. -/
theorem end5M_satisfies_1 :
    Satisfies (Magma.end5M 0) [
      52, 412, 415, 418, 420, 421, 423, 424, 425, 428, 618, 621, 625, 626, 627, 628, 629, 824,
      837, 839, 852, 1024, 1027, 1032, 1259, 1260, 2036, 3723
    ] := by decide!
