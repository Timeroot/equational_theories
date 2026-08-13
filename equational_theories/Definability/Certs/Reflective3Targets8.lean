import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 9 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_8 :
    FamilyRefutes Magma.reflective3 [
      1748, 1749, 1751, 1752, 1753, 1754, 1756, 1757, 1758, 1760, 1762, 1764, 1765, 1766, 1768,
      1769, 1770, 1771, 1773, 1775, 1777, 1778, 1779, 1781, 1782, 1783, 1785, 1786, 1787, 1788,
      1790, 1791, 1792, 1794, 1795, 1796, 1798, 1799, 1800, 1802, 1803, 1804, 1805, 1807, 1808,
      1809, 1810, 1812, 1813, 1814, 1815, 1817, 1818, 1819, 1820, 1822, 1823, 1824, 1825, 1827,
      1828, 1829, 1830, 1831, 1885, 1886, 1889, 1891, 1892, 1893, 1896, 1899, 1901, 1903, 1905,
      1906, 1907, 1909, 1911, 1913, 1914, 1915, 1917, 1918, 1919, 1920, 1923, 1926, 1928, 1930,
      1933, 1935, 1936, 1938, 1939, 1940, 1942, 1944, 1946, 1947
    ] := by decide!
