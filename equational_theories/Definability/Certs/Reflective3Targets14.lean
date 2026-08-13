import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 15 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_14 :
    FamilyRefutes Magma.reflective3 [
      2926, 2928, 2929, 2930, 2932, 2933, 2934, 2935, 2937, 2938, 2941, 2943, 2945, 2948, 2950,
      2951, 2953, 2954, 2955, 2957, 2959, 2961, 2962, 2963, 2965, 2966, 2967, 2969, 2970, 2971,
      2972, 2974, 2975, 2976, 2978, 2980, 2982, 2983, 2984, 2986, 2987, 2988, 2989, 2991, 2993,
      2995, 2996, 2997, 2999, 3000, 3001, 3003, 3004, 3005, 3006, 3008, 3009, 3010, 3012, 3013,
      3014, 3016, 3017, 3018, 3020, 3021, 3022, 3023, 3025, 3026, 3027, 3028, 3030, 3031, 3032,
      3033, 3035, 3036, 3037, 3038, 3040, 3041, 3042, 3043, 3045, 3046, 3047, 3048, 3049, 3104,
      3106, 3107, 3109, 3110, 3111, 3114, 3117, 3119, 3121, 3123
    ] := by decide!
