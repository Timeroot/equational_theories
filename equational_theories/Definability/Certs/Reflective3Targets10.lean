import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 11 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_10 :
    FamilyRefutes Magma.reflective3 [
      2142, 2143, 2145, 2146, 2147, 2149, 2150, 2151, 2153, 2154, 2155, 2157, 2158, 2159, 2160,
      2162, 2163, 2164, 2166, 2168, 2171, 2172, 2174, 2175, 2176, 2177, 2179, 2181, 2183, 2184,
      2185, 2187, 2188, 2189, 2191, 2192, 2193, 2194, 2197, 2198, 2200, 2201, 2202, 2204, 2205,
      2206, 2208, 2209, 2210, 2211, 2213, 2214, 2215, 2216, 2218, 2219, 2220, 2221, 2223, 2224,
      2225, 2226, 2228, 2229, 2230, 2231, 2233, 2234, 2235, 2236, 2237, 2292, 2294, 2295, 2297,
      2298, 2299, 2301, 2302, 2304, 2305, 2307, 2308, 2309, 2311, 2312, 2313, 2315, 2316, 2317,
      2319, 2320, 2321, 2323, 2324, 2325, 2326, 2328, 2329, 2332
    ] := by decide!
