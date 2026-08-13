import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.affine5` (part 4 of 4)

Equations with no model among the `5` magmas on `Fin 5` with all of `F₂₀ = AGL(1, 5)` as
automorphisms. There are `2471` such equations in all, of which `71` are listed here; each of them
is a valid *target* `L` of a `Magma.affine5` certificate, and so is not definable from any of the
`2223` source laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `5` magmas on `Fin 5` with all of `F₂₀ = AGL(1, 5)` as automorphisms satisfies any
of these `71` equations. -/
theorem affine5_refutes_3 :
    FamilyRefutes Magma.affine5 [
      4570, 4571, 4572, 4573, 4575, 4576, 4577, 4578, 4580, 4581, 4582, 4588, 4589, 4591, 4592,
      4594, 4595, 4596, 4607, 4609, 4610, 4612, 4613, 4614, 4616, 4617, 4618, 4620, 4621, 4623,
      4624, 4626, 4627, 4628, 4637, 4639, 4640, 4641, 4643, 4644, 4646, 4647, 4648, 4650, 4651,
      4652, 4653, 4658, 4659, 4660, 4661, 4662, 4664, 4665, 4667, 4668, 4670, 4671, 4678, 4679,
      4680, 4681, 4683, 4685, 4686, 4687, 4688, 4690, 4691, 4692, 4694
    ] := by decide!
