import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 2 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_1 :
    FamilyRefutes Magma.reflective3 [
      240, 241, 243, 244, 245, 247, 248, 249, 251, 252, 253, 254, 272, 275, 277, 278, 279, 282,
      284, 285, 287, 288, 289, 291, 292, 293, 295, 296, 297, 299, 300, 301, 303, 304, 305, 306,
      465, 467, 468, 470, 471, 472, 475, 478, 480, 481, 482, 484, 485, 486, 488, 490, 493, 494,
      496, 497, 498, 499, 501, 502, 505, 507, 509, 512, 514, 515, 517, 518, 519, 521, 523, 525,
      526, 527, 529, 530, 531, 533, 534, 535, 536, 538, 539, 540, 542, 544, 546, 547, 548, 550,
      551, 552, 553, 555, 556, 557, 559, 560, 561, 563
    ] := by decide!
