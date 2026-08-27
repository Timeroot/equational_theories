import equational_theories.Definability.ExactEnd5M

/-!
# Term-structural certificate targets: `Magma.end5M`

Equations with no model among the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`25` monoid of `Magma.endE5M`. `16` of them are worth listing, of which `16` appear here; each
is a valid *target* `L` of a `Magma.end5M` certificate, and so is not term-structural from any of
the `64` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`25` monoid of
`Magma.endE5M` satisfies any of these `16` equations. -/
theorem end5M_refutes_0 :
    FamilyRefutes Magma.end5M [
      825, 828, 1227, 1230, 1233, 1236, 2310, 2347, 2364, 2398, 2669, 2679, 3460, 3529, 3897, 3931
    ] := by nativeDecideFin!
