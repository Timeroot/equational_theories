import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 10 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_9 :
    FamilyRefutes Magma.reflective3 [
      1948, 1950, 1951, 1952, 1954, 1955, 1956, 1957, 1959, 1960, 1961, 1963, 1965, 1967, 1968,
      1969, 1971, 1972, 1973, 1974, 1976, 1978, 1980, 1981, 1982, 1984, 1985, 1986, 1988, 1989,
      1990, 1991, 1993, 1994, 1995, 1997, 1998, 1999, 2001, 2002, 2003, 2005, 2006, 2007, 2008,
      2010, 2011, 2012, 2013, 2015, 2016, 2017, 2018, 2020, 2021, 2022, 2023, 2025, 2026, 2027,
      2028, 2030, 2031, 2032, 2033, 2034, 2089, 2091, 2092, 2094, 2095, 2096, 2098, 2099, 2101,
      2102, 2104, 2105, 2106, 2108, 2109, 2110, 2112, 2113, 2114, 2116, 2117, 2118, 2120, 2121,
      2122, 2123, 2126, 2129, 2131, 2133, 2136, 2138, 2139, 2141
    ] := by decide!
