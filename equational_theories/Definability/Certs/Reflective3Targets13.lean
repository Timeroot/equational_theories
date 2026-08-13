import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 14 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_13 :
    FamilyRefutes Magma.reflective3 [
      2732, 2735, 2738, 2740, 2742, 2744, 2745, 2747, 2748, 2750, 2751, 2752, 2754, 2755, 2756,
      2758, 2759, 2760, 2762, 2763, 2764, 2766, 2767, 2768, 2769, 2771, 2772, 2773, 2775, 2776,
      2777, 2780, 2781, 2783, 2784, 2785, 2786, 2788, 2789, 2790, 2792, 2793, 2794, 2796, 2797,
      2798, 2800, 2801, 2802, 2803, 2805, 2806, 2807, 2809, 2810, 2811, 2813, 2814, 2815, 2817,
      2818, 2819, 2820, 2822, 2823, 2824, 2825, 2827, 2828, 2829, 2830, 2832, 2833, 2834, 2835,
      2837, 2838, 2839, 2840, 2842, 2843, 2844, 2845, 2846, 2900, 2901, 2903, 2904, 2906, 2907,
      2908, 2910, 2911, 2914, 2916, 2918, 2920, 2921, 2922, 2924
    ] := by decide!
