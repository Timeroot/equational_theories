import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 13 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_12 :
    FamilyRefutes Magma.reflective3 [
      2531, 2532, 2535, 2537, 2539, 2542, 2544, 2545, 2547, 2548, 2549, 2551, 2553, 2555, 2556,
      2557, 2559, 2560, 2561, 2563, 2564, 2565, 2566, 2568, 2569, 2570, 2572, 2574, 2577, 2578,
      2580, 2581, 2582, 2583, 2585, 2586, 2587, 2589, 2590, 2591, 2593, 2594, 2595, 2597, 2598,
      2599, 2600, 2603, 2604, 2606, 2607, 2608, 2610, 2611, 2612, 2614, 2615, 2616, 2617, 2619,
      2620, 2621, 2622, 2624, 2625, 2626, 2627, 2629, 2630, 2631, 2632, 2634, 2635, 2636, 2637,
      2639, 2640, 2641, 2642, 2643, 2698, 2701, 2703, 2704, 2705, 2708, 2711, 2713, 2715, 2717,
      2718, 2719, 2721, 2722, 2723, 2726, 2727, 2729, 2730, 2731
    ] := by decide!
