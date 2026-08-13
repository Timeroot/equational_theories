import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.cyclic3` (part 7 of 7)

Equations with no model among the `27` magmas on `Fin 3` with `x ↦ x + 1` as an automorphism.
There are `2446` such equations in all, of which `46` are listed here; each of them is a valid
*target* `L` of a `Magma.cyclic3` certificate, and so is not definable from any of the `2248`
source laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `27` magmas on `Fin 3` with `x ↦ x + 1` as an automorphism satisfies any of these
`46` equations. -/
theorem cyclic3_refutes_6 :
    FamilyRefutes Magma.cyclic3 [
      4614, 4616, 4617, 4618, 4620, 4621, 4623, 4624, 4626, 4627, 4628, 4637, 4639, 4641, 4643,
      4644, 4646, 4648, 4650, 4651, 4652, 4653, 4659, 4660, 4661, 4662, 4664, 4665, 4667, 4668,
      4670, 4671, 4678, 4679, 4680, 4681, 4683, 4684, 4685, 4686, 4687, 4688, 4690, 4691, 4692,
      4694
    ] := by decide!
