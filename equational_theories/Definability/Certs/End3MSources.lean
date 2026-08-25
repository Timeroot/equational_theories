import equational_theories.Definability.ExactEnd3M

/-!
# Term-structural certificate sources: `Magma.end3M`

For each of the following magmas, drawn from the `5` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`2` monoid of `Magma.endE3M`, the equations it satisfies that no earlier listed
magma does. Together they are the `96` equations that are worth using as the *source* `L'` of a
`Magma.end3M` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `73` equations satisfied by `Magma.end3M 4`, and by no earlier member of the cover. -/
theorem end3M_satisfies_0 :
    Satisfies (Magma.end3M 4) [
      1, 43, 1426, 1442, 1444, 1445, 1479, 1481, 1482, 1629, 1647, 1654, 1657, 1684, 1691, 1694,
      1832, 1838, 1840, 1848, 1850, 1858, 1860, 2035, 2051, 2053, 2088, 2090, 2125, 2127, 3253,
      3258, 3259, 3261, 3306, 3308, 3353, 3355, 3456, 3457, 3459, 3462, 3511, 3518, 3549, 3556,
      3862, 3877, 3880, 3887, 3917, 3924, 3955, 3962, 4065, 4067, 4073, 4083, 4127, 4131, 4154,
      4158, 4283, 4358, 4380, 4398, 4405, 4435, 4442, 4482, 4531, 4544, 4677
    ] := by decide!

/-- `23` equations satisfied by `Magma.end3M 0`, and by no earlier member of the cover. -/
theorem end3M_satisfies_1 :
    Satisfies (Magma.end3M 0) [
      3262, 3309, 3352, 3465, 3521, 3546, 3890, 3927, 3952, 4093, 4121, 4164, 4276, 4284, 4314,
      4389, 4408, 4445, 4472, 4479, 4591, 4599, 4606
    ] := by decide!
