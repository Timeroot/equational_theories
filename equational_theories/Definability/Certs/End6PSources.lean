import equational_theories.Definability.ExactEnd6P

/-!
# Term-structural certificate sources: `Magma.end6P`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`114` monoid of `Magma.endE6P`, the equations it satisfies that no earlier listed
magma does. Together they are the `52` equations that are worth using as the *source* `L'` of a
`Magma.end6P` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `29` equations satisfied by `Magma.end6P 0`, and by no earlier member of the cover. -/
theorem end6P_satisfies_0 :
    Satisfies (Magma.end6P 0) [
      317, 3270, 3280, 3283, 3287, 3299, 3483, 3490, 3493, 3505, 3885, 3889, 3896, 3912, 4277,
      4294, 4299, 4308, 4312, 4392, 4410, 4417, 4423, 4425, 4426, 4429, 4475, 4495, 4503
    ] := by decide!

/-- `23` equations satisfied by `Magma.end6P 1`, and by no earlier member of the cover. -/
theorem end6P_satisfies_1 :
    Satisfies (Magma.end6P 1) [
      372, 3479, 3506, 3882, 3904, 4082, 4088, 4110, 4111, 4115, 4393, 4447, 4457, 4460, 4462,
      4463, 4467, 4487, 4489, 4504, 4595, 4661, 4670
    ] := by decide!
