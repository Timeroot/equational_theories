import equational_theories.Definability.ExactEnd6AG

/-!
# Term-structural certificate targets: `Magma.end6AG`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`180` monoid of `Magma.endE6AG`. `24` of them are worth listing, of which `24` appear here;
each is a valid *target* `L` of a `Magma.end6AG` certificate, and so is not term-structural from any
of the `10` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`180` monoid of
`Magma.endE6AG` satisfies any of these `24` equations. -/
theorem end6AG_refutes_0 :
    FamilyRefutes Magma.end6AG [
      323, 378, 1647, 1850, 3316, 3461, 3475, 3519, 3724, 3749, 3864, 3888, 3925, 4128, 4269,
      4314, 4316, 4320, 4321, 4584, 4598, 4606, 4631, 4636
    ] := by nativeDecideFin!
