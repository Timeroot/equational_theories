import equational_theories.Definability.ExactEnd6I

/-!
# Term-structural certificate sources: `Magma.end6I`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`28` monoid of `Magma.endE6I`, the equations it satisfies that no earlier listed
magma does. Together they are the `93` equations that are worth using as the *source* `L'` of a
`Magma.end6I` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `50` equations satisfied by `Magma.end6I 0`, and by no earlier member of the cover. -/
theorem end6I_satisfies_0 :
    Satisfies (Magma.end6I 0) [
      108, 109, 111, 437, 443, 844, 847, 848, 849, 851, 858, 1025, 1031, 1039, 1042, 1046, 1049,
      1052, 1053, 1056, 1060, 1064, 1068, 1230, 1234, 1239, 1242, 1243, 1245, 1250, 1251, 1252,
      1253, 1254, 1255, 1256, 1257, 1259, 1262, 1263, 1264, 1265, 1267, 1271, 1835, 1861, 1865,
      3322, 3662, 3729
    ] := by decide!

/-- `43` equations satisfied by `Magma.end6I 2`, and by no earlier member of the cover. -/
theorem end6I_satisfies_1 :
    Satisfies (Magma.end6I 2) [
      231, 242, 246, 1718, 1731, 1746, 2266, 2273, 2277, 2281, 2293, 2310, 2314, 2318, 2330,
      2351, 2368, 2372, 2385, 2389, 2402, 2406, 2420, 2425, 2430, 2506, 2517, 2533, 2554, 2558,
      2571, 2588, 2623, 2724, 2761, 2791, 2812, 2836, 3115, 3197, 3684, 3820, 4138
    ] := by decide!
