import equational_theories.Definability.ExactEnd5F

/-!
# Term-structural certificate targets: `Magma.end5F`

Equations with no model among the `8` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`13` monoid of `Magma.endE5F`. `34` of them are worth listing, of which `34` appear here; each
is a valid *target* `L` of a `Magma.end5F` certificate, and so is not term-structural from any of
the `168` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `8` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`13` monoid of
`Magma.endE5F` satisfies any of these `34` equations. -/
theorem end5F_refutes_0 :
    FamilyRefutes Magma.end5F [
      326, 375, 639, 716, 825, 906, 919, 1023, 1109, 1451, 1528, 2043, 2064, 2444, 2530, 2647,
      2669, 2673, 2855, 2876, 3481, 3558, 3667, 3722, 3748, 3761, 3865, 3951, 4290, 4369, 4408,
      4479, 4605, 4684
    ] := by nativeDecideFin!
