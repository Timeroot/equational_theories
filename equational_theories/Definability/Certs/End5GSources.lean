import equational_theories.Definability.ExactEnd5G

/-!
# Term-structural certificate sources: `Magma.end5G`

For each of the following magmas, drawn from the `2` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`17` monoid of `Magma.endE5G`, the equations it satisfies that no earlier listed
magma does. Together they are the `76` equations that are worth using as the *source* `L'` of a
`Magma.end5G` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `42` equations satisfied by `Magma.end5G 1`, and by no earlier member of the cover. -/
theorem end5G_satisfies_0 :
    Satisfies (Magma.end5G 1) [
      242, 309, 319, 2277, 2314, 2351, 2368, 2372, 2402, 2420, 2425, 2506, 2517, 2554, 2558,
      2571, 2588, 2623, 3115, 3197, 3265, 3274, 3275, 3285, 3289, 3290, 3301, 3302, 3478, 3488,
      3492, 3496, 3504, 4105, 4138, 4279, 4318, 4324, 4327, 4331, 4336, 4337
    ] := by decide!

/-- `34` equations satisfied by `Magma.end5G 0`, and by no earlier member of the cover. -/
theorem end5G_satisfies_1 :
    Satisfies (Magma.end5G 0) [
      111, 361, 371, 443, 1042, 1046, 1052, 1053, 1056, 1060, 1068, 1243, 1245, 1259, 1262, 1263,
      1265, 1271, 3322, 3884, 3894, 3898, 3902, 3910, 4085, 4087, 4101, 4107, 4113, 4594, 4616,
      4626, 4639, 4651
    ] := by decide!
