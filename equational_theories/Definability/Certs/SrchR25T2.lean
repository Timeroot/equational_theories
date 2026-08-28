import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 3 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `16`
equations here, 3,315 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1662 takes them (139 nodes). -/
def ordSR25_Law1662 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1662. -/
theorem noSR25_Law1662 : ∀ v : Magma.tupR25,
    ¬ @Equation1662 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1731 takes them (133 nodes). -/
def ordSR25_Law1731 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1731. -/
theorem noSR25_Law1731 : ∀ v : Magma.tupR25,
    ¬ @Equation1731 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1731) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1731) (by native_decide) v.1 v.2
    ((@Law1731.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (125 nodes). -/
def ordSR25_Law1780 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1780. -/
theorem noSR25_Law1780 : ∀ v : Magma.tupR25,
    ¬ @Equation1780 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1861 takes them (153 nodes). -/
def ordSR25_Law1861 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1861. -/
theorem noSR25_Law1861 : ∀ v : Magma.tupR25,
    ¬ @Equation1861 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1861) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1861) (by native_decide) v.1 v.2
    ((@Law1861.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (145 nodes). -/
def ordSR25_Law1873 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1873. -/
theorem noSR25_Law1873 : ∀ v : Magma.tupR25,
    ¬ @Equation1873 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (214 nodes). -/
def ordSR25_Law1934 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1934. -/
theorem noSR25_Law1934 : ∀ v : Magma.tupR25,
    ¬ @Equation1934 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (125 nodes). -/
def ordSR25_Law1949 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1949. -/
theorem noSR25_Law1949 : ∀ v : Magma.tupR25,
    ¬ @Equation1949 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2043 takes them (310 nodes). -/
def ordSR25_Law2043 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2043. -/
theorem noSR25_Law2043 : ∀ v : Magma.tupR25,
    ¬ @Equation2043 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2043) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2043) (by native_decide) v.1 v.2
    ((@Law2043.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2056 takes them (150 nodes). -/
def ordSR25_Law2056 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2056. -/
theorem noSR25_Law2056 : ∀ v : Magma.tupR25,
    ¬ @Equation2056 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2056) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law2056) (by native_decide) v.1 v.2
    ((@Law2056.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (214 nodes). -/
def ordSR25_Law2137 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2137. -/
theorem noSR25_Law2137 : ∀ v : Magma.tupR25,
    ¬ @Equation2137 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2241 takes them (199 nodes). -/
def ordSR25_Law2241 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2241. -/
theorem noSR25_Law2241 : ∀ v : Magma.tupR25,
    ¬ @Equation2241 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2241) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2241) (by native_decide) v.1 v.2
    ((@Law2241.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2244 takes them (324 nodes). -/
def ordSR25_Law2244 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2244. -/
theorem noSR25_Law2244 : ∀ v : Magma.tupR25,
    ¬ @Equation2244 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2244) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2244) (by native_decide) v.1 v.2
    ((@Law2244.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (234 nodes). -/
def ordSR25_Law2267 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2267. -/
theorem noSR25_Law2267 : ∀ v : Magma.tupR25,
    ¬ @Equation2267 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2447 takes them (348 nodes). -/
def ordSR25_Law2447 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2447. -/
theorem noSR25_Law2447 : ∀ v : Magma.tupR25,
    ¬ @Equation2447 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2447) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2447) (by native_decide) v.1 v.2
    ((@Law2447.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (259 nodes). -/
def ordSR25_Law2457 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2457. -/
theorem noSR25_Law2457 : ∀ v : Magma.tupR25,
    ¬ @Equation2457 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (243 nodes). -/
def ordSR25_Law2470 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2470. -/
theorem noSR25_Law2470 : ∀ v : Magma.tupR25,
    ¬ @Equation2470 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srchR25_refutes_2 :
    FamilyRefutes Magma.srchR25 [
      1662, 1731, 1780, 1861, 1873, 1934, 1949, 2043, 2056, 2137, 2241, 2244, 2267, 2447, 2457,
      2470
    ] :=
  ⟨noSR25_Law1662, noSR25_Law1731, noSR25_Law1780, noSR25_Law1861, noSR25_Law1873, noSR25_Law1934, noSR25_Law1949, noSR25_Law2043, noSR25_Law2056, noSR25_Law2137, noSR25_Law2241, noSR25_Law2244, noSR25_Law2267, noSR25_Law2447, noSR25_Law2457, noSR25_Law2470⟩
