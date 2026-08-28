import equational_theories.Definability.ExactEnd6AF

/-!
# Term-structural certificate targets: `Magma.end6AF`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`30` monoid of `Magma.endE6AF`. `9` of them are worth listing, of which `9` appear here; each
is a valid *target* `L` of a `Magma.end6AF` certificate, and so is not term-structural from any of
the `14` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`30` monoid of
`Magma.endE6AF` satisfies any of these `9` equations. -/
theorem end6AF_refutes_0 :
    FamilyRefutes Magma.end6AF [
      3278, 3306, 3316, 4068, 4128, 4131, 4396, 4399, 4473
    ] := by nativeDecideFin!
