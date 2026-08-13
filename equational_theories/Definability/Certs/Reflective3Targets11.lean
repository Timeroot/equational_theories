import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 12 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_11 :
    FamilyRefutes Magma.reflective3 [
      2334, 2336, 2339, 2341, 2342, 2344, 2345, 2346, 2348, 2350, 2352, 2353, 2354, 2356, 2357,
      2358, 2360, 2361, 2362, 2363, 2365, 2366, 2367, 2369, 2370, 2371, 2374, 2375, 2377, 2378,
      2379, 2380, 2382, 2383, 2384, 2386, 2387, 2388, 2390, 2391, 2392, 2394, 2395, 2396, 2397,
      2400, 2401, 2403, 2404, 2405, 2407, 2408, 2409, 2411, 2412, 2413, 2414, 2416, 2417, 2418,
      2419, 2421, 2422, 2423, 2424, 2426, 2427, 2428, 2429, 2431, 2432, 2433, 2434, 2436, 2437,
      2438, 2439, 2440, 2495, 2497, 2498, 2500, 2501, 2502, 2505, 2508, 2510, 2511, 2512, 2514,
      2515, 2516, 2518, 2520, 2523, 2524, 2526, 2527, 2528, 2529
    ] := by decide!
