import equational_theories.Definability.ExactAut6S3wr6

/-!
# Structural certificate targets: `Magma.exactS3wr6` (part 1 of 1)

Equations with no model among the `4` magmas on `Fin 6` whose automorphism group is exactly the
order-`72` group of `Magma.permES3wr6`. `18` of them are worth listing, of which `18` appear here;
each is a valid *target* `L` of a `Magma.exactS3wr6` certificate, and so is not structural from any
of the `212` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose automorphism group is exactly the order-`72` group of
`Magma.permES3wr6` satisfies any of these `18` equations. -/
theorem exactS3wr6_refutes_0 :
    FamilyRefutes Magma.exactS3wr6 [
      333, 377, 3318, 3343, 3346, 3521, 3546, 3721, 3759, 3927, 3952, 4120, 4130, 4155, 4291,
      4314, 4320, 4445
    ] := by nativeDecideFin!
