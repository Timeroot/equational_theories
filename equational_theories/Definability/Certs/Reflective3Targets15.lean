import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 16 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `92` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these `92`
equations. -/
theorem reflective3_refutes_15 :
    FamilyRefutes Magma.reflective3 [
      3124, 3125, 3127, 3128, 3129, 3132, 3133, 3135, 3136, 3137, 3138, 3140, 3141, 3144, 3146,
      3148, 3151, 3153, 3154, 3156, 3157, 3158, 3160, 3161, 3162, 3164, 3165, 3166, 3168, 3169,
      3170, 3172, 3173, 3174, 3175, 3177, 3178, 3179, 3181, 3183, 3185, 3186, 3187, 3189, 3190,
      3191, 3192, 3194, 3196, 3198, 3199, 3200, 3202, 3203, 3204, 3206, 3207, 3208, 3209, 3212,
      3213, 3215, 3216, 3217, 3219, 3220, 3221, 3223, 3224, 3225, 3226, 3228, 3229, 3230, 3231,
      3233, 3234, 3235, 3236, 3238, 3239, 3240, 3241, 3243, 3244, 3245, 3246, 3248, 3249, 3250,
      3251, 3252
    ] := by decide!
