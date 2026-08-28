import equational_theories.Definability.ExactEnd6F

/-!
# Term-structural certificate targets: `Magma.end6F`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`144` monoid of `Magma.endE6F`. `79` of them are worth listing, of which `79` appear here;
each is a valid *target* `L` of a `Magma.end6F` certificate, and so is not term-structural from any
of the `181` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`144` monoid of
`Magma.endE6F` satisfies any of these `79` equations. -/
theorem end6F_refutes_0 :
    FamilyRefutes Magma.end6F [
      43, 323, 325, 326, 375, 378, 385, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3322, 3323,
      3326, 3334, 3342, 3346, 3353, 3355, 3509, 3511, 3512, 3515, 3518, 3519, 3521, 3522, 3525,
      3529, 3533, 3537, 3541, 3545, 3549, 3556, 3558, 3712, 3721, 3724, 3725, 3729, 3749, 3759,
      3820, 3915, 3917, 3918, 3921, 3924, 3925, 3928, 3931, 3935, 3939, 3943, 3947, 3951, 3952,
      3955, 3962, 3964, 4118, 4120, 4121, 4127, 4128, 4131, 4134, 4138, 4146, 4154, 4155, 4158,
      4165, 4167, 4226
    ] := by nativeDecideFin!
