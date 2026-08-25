import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 3 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `63` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `63` equations. -/
theorem exactC45_refutes_2 :
    FamilyRefutes Magma.exactC45 [
      1247, 1261, 1323, 1457, 1461, 1489, 1516, 1526, 1577, 1590, 1648, 1656, 1659, 1660, 1661,
      1663, 1668, 1685, 1692, 1742, 1763, 1797, 1816, 1852, 1862, 1871, 1872, 1874, 1875, 1895,
      1912, 1922, 1924, 1979, 2000, 2024, 2046, 2076, 2079, 2091, 2098, 2101, 2304, 2322, 2333,
      2376, 2450, 2463, 2473, 2477, 2481, 2489, 2536, 2670, 2677, 2685, 2744, 2782, 2888, 2891,
      3277, 3291, 3300
    ] := by nativeDecideFin!
