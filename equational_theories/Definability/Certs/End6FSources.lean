import equational_theories.Definability.ExactEnd6F

/-!
# Term-structural certificate sources: `Magma.end6F`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`144` monoid of `Magma.endE6F`, the equations it satisfies that no earlier listed
magma does. Together they are the `181` equations that are worth using as the *source* `L'` of a
`Magma.end6F` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `181` equations satisfied by `Magma.end6F 0`, and by no earlier member of the cover. -/
theorem end6F_satisfies_0 :
    Satisfies (Magma.end6F 0) [
      314, 321, 373, 3273, 3277, 3291, 3295, 3304, 3476, 3480, 3494, 3498, 3507, 3676, 3681,
      3683, 3695, 3697, 3705, 3707, 3886, 3899, 3900, 4089, 4102, 4103, 4114, 4116, 4274, 4281,
      4292, 4295, 4298, 4302, 4303, 4306, 4309, 4313, 4322, 4326, 4328, 4329, 4333, 4335, 4338,
      4344, 4345, 4347, 4349, 4350, 4352, 4353, 4356, 4363, 4366, 4368, 4371, 4372, 4373, 4375,
      4376, 4377, 4379, 4387, 4400, 4404, 4407, 4411, 4414, 4418, 4419, 4422, 4427, 4428, 4431,
      4444, 4451, 4453, 4455, 4459, 4468, 4481, 4485, 4488, 4492, 4493, 4496, 4501, 4505, 4513,
      4517, 4519, 4521, 4522, 4523, 4524, 4526, 4527, 4528, 4530, 4532, 4533, 4534, 4535, 4536,
      4537, 4538, 4539, 4540, 4543, 4545, 4547, 4548, 4549, 4551, 4552, 4553, 4555, 4556, 4557,
      4558, 4559, 4560, 4561, 4562, 4563, 4564, 4565, 4566, 4567, 4568, 4569, 4570, 4571, 4572,
      4573, 4575, 4576, 4577, 4578, 4579, 4580, 4581, 4582, 4589, 4596, 4607, 4610, 4613, 4617,
      4618, 4621, 4624, 4628, 4637, 4641, 4643, 4644, 4648, 4650, 4653, 4659, 4660, 4662, 4664,
      4665, 4667, 4668, 4671, 4678, 4680, 4681, 4683, 4685, 4686, 4687, 4688, 4690, 4691, 4692,
      4694
    ] := by decide!
