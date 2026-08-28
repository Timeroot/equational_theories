import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 9 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 3,458 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2078 takes them (236 nodes). -/
def ordS8R52_Law2078 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2078. -/
theorem noS8R52_Law2078 : ∀ v : Magma.tup8R52,
    ¬ @Equation2078 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2078) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2078) (by native_decide) v.1 v.2
    ((@Law2078.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (577 nodes). -/
def ordS8R52_Law2137 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2137. -/
theorem noS8R52_Law2137 : ∀ v : Magma.tup8R52,
    ¬ @Equation2137 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2152 takes them (225 nodes). -/
def ordS8R52_Law2152 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2152. -/
theorem noS8R52_Law2152 : ∀ v : Magma.tup8R52,
    ¬ @Equation2152 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2152) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2152) (by native_decide) v.1 v.2
    ((@Law2152.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2182 takes them (217 nodes). -/
def ordS8R52_Law2182 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2182. -/
theorem noS8R52_Law2182 : ∀ v : Magma.tup8R52,
    ¬ @Equation2182 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2182) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2182) (by native_decide) v.1 v.2
    ((@Law2182.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2203 takes them (225 nodes). -/
def ordS8R52_Law2203 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2203. -/
theorem noS8R52_Law2203 : ∀ v : Magma.tup8R52,
    ¬ @Equation2203 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2203) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2203) (by native_decide) v.1 v.2
    ((@Law2203.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2227 takes them (193 nodes). -/
def ordS8R52_Law2227 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2227. -/
theorem noS8R52_Law2227 : ∀ v : Magma.tup8R52,
    ¬ @Equation2227 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2227) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2227) (by native_decide) v.1 v.2
    ((@Law2227.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2264 takes them (477 nodes). -/
def ordS8R52_Law2264 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2264. -/
theorem noS8R52_Law2264 : ∀ v : Magma.tup8R52,
    ¬ @Equation2264 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2264) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2264) (by native_decide) v.1 v.2
    ((@Law2264.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (601 nodes). -/
def ordS8R52_Law2267 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2267. -/
theorem noS8R52_Law2267 : ∀ v : Magma.tup8R52,
    ¬ @Equation2267 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2270 takes them (249 nodes). -/
def ordS8R52_Law2270 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2270. -/
theorem noS8R52_Law2270 : ∀ v : Magma.tup8R52,
    ¬ @Equation2270 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2270) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2270) (by native_decide) v.1 v.2
    ((@Law2270.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2274 takes them (217 nodes). -/
def ordS8R52_Law2274 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2274. -/
theorem noS8R52_Law2274 : ∀ v : Magma.tup8R52,
    ¬ @Equation2274 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2274) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2274) (by native_decide) v.1 v.2
    ((@Law2274.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2278 takes them (241 nodes). -/
def ordS8R52_Law2278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2278. -/
theorem noS8R52_Law2278 : ∀ v : Magma.tup8R52,
    ¬ @Equation2278 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2278) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2278) (by native_decide) v.1 v.2
    ((@Law2278.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch8R52_refutes_8 :
    FamilyRefutes Magma.srch8R52 [
      2078, 2137, 2152, 2182, 2203, 2227, 2264, 2267, 2270, 2274, 2278
    ] :=
  ⟨noS8R52_Law2078, noS8R52_Law2137, noS8R52_Law2152, noS8R52_Law2182, noS8R52_Law2203, noS8R52_Law2227, noS8R52_Law2264, noS8R52_Law2267, noS8R52_Law2270, noS8R52_Law2274, noS8R52_Law2278⟩
