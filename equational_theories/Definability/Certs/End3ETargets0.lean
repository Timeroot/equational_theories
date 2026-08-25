import equational_theories.Definability.ExactEnd3E

/-!
# Term-structural certificate targets: `Magma.end3E`

Equations with no model among the `18` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`3` monoid of `Magma.endE3E`. `113` of them are worth listing, of which `113` appear here;
each is a valid *target* `L` of a `Magma.end3E` certificate, and so is not term-structural from any
of the `1052` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `18` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`3` monoid of
`Magma.endE3E` satisfies any of these `113` equations. -/
theorem end3E_refutes_0 :
    FamilyRefutes Magma.end3E [
      3, 9, 28, 48, 50, 51, 102, 151, 152, 166, 228, 270, 280, 290, 332, 333, 377, 387, 412, 414,
      415, 418, 420, 421, 422, 423, 424, 425, 615, 618, 621, 623, 624, 626, 627, 628, 826, 829,
      1021, 1024, 1026, 1032, 1039, 1232, 1429, 1430, 1634, 1701, 1837, 1839, 2124, 2161, 2337,
      2493, 2503, 2533, 2567, 2584, 2743, 2787, 2899, 2919, 2946, 2956, 2973, 2990, 3007, 3024,
      3085, 3102, 3122, 3139, 3149, 3159, 3176, 3193, 3210, 3227, 3343, 3346, 3546, 3659, 3660,
      3674, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3749, 3751, 3752, 3758, 3759, 3927, 4120,
      4130, 4290, 4396, 4399, 4406, 4408, 4433, 4436, 4443, 4445, 4472, 4473, 4479, 4480, 4605
    ] := by nativeDecideFin!
