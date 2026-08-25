import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 1 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `46` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `46` equations. -/
theorem exactC45_refutes_0 :
    FamilyRefutes Magma.exactC45 [
      41, 44, 46, 63, 73, 106, 118, 124, 125, 206, 222, 224, 229, 271, 274, 314, 318, 321, 334,
      336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353,
      354, 355, 356, 357, 358, 363, 366, 373, 374
    ] := by nativeDecideFin!
