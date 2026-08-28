import equational_theories.Definability.ExactEnd6H

/-!
# Term-structural certificate sources: `Magma.end6H`

For each of the following magmas, drawn from the `16` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`70` monoid of `Magma.endE6H`, the equations it satisfies that no earlier listed
magma does. Together they are the `106` equations that are worth using as the *source* `L'` of a
`Magma.end6H` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `50` equations satisfied by `Magma.end6H 2`, and by no earlier member of the cover. -/
theorem end6H_satisfies_0 :
    Satisfies (Magma.end6H 2) [
      311, 377, 379, 3260, 3267, 3470, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729,
      3730, 3866, 3869, 3872, 3874, 3875, 3876, 4128, 4129, 4130, 4132, 4133, 4134, 4135, 4136,
      4271, 4285, 4289, 4315, 4317, 4319, 4339, 4342, 4357, 4359, 4361, 4397, 4434, 4471, 4506,
      4507, 4509, 4630, 4654, 4672
    ] := by decide!

/-- `49` equations satisfied by `Magma.end6H 12`, and by no earlier member of the cover. -/
theorem end6H_satisfies_1 :
    Satisfies (Magma.end6H 12) [
      333, 343, 370, 3316, 3326, 3343, 3363, 3380, 3397, 3414, 3431, 3477, 3487, 3491, 3495,
      3499, 3503, 3712, 3732, 3749, 3759, 3769, 3786, 3803, 3820, 3837, 3909, 4086, 4112, 4300,
      4330, 4374, 4391, 4486, 4490, 4494, 4498, 4502, 4593, 4615, 4625, 4638, 4645, 4649, 4663,
      4669, 4682, 4689, 4693
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6H 0`, and by no earlier member of the cover. -/
theorem end6H_satisfies_2 :
    Satisfies (Magma.end6H 0) [
      3512, 3513, 3919, 4400
    ] := by decide!

/-- `3` equations satisfied by `Magma.end6H 4`, and by no earlier member of the cover. -/
theorem end6H_satisfies_3 :
    Satisfies (Magma.end6H 4) [
      3587, 3993, 4533
    ] := by decide!
