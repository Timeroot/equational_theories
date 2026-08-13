import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 1 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_0 :
    FamilyRefutes Magma.reflective3 [
      2, 6, 7, 15, 17, 18, 20, 21, 22, 30, 32, 33, 35, 36, 37, 64, 67, 69, 70, 71, 74, 76, 77, 79,
      80, 81, 83, 84, 85, 87, 88, 89, 91, 92, 93, 95, 96, 97, 98, 116, 119, 121, 122, 123, 126,
      128, 129, 131, 132, 133, 135, 136, 137, 139, 140, 141, 143, 144, 145, 147, 148, 149, 150,
      167, 168, 171, 173, 174, 175, 178, 180, 181, 183, 184, 185, 187, 188, 189, 191, 192, 193,
      195, 196, 197, 199, 200, 201, 202, 220, 223, 225, 226, 227, 230, 232, 233, 235, 236, 237, 239
    ] := by decide!
