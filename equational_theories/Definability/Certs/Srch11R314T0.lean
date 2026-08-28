import equational_theories.Definability.Srch_S11R314

/-!
# Structural certificate targets: `Magma.srch11R314`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R314_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 192 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R314_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 676 takes them (15 nodes). -/
def ordS11R314_Law676 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 676. -/
theorem noS11R314_Law676 : ∀ v : Magma.tup11R314,
    ¬ @Equation676 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law676) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law676) (by native_decide) v.1 v.2
    ((@Law676.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1046 takes them (15 nodes). -/
def ordS11R314_Law1046 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1046. -/
theorem noS11R314_Law1046 : ∀ v : Magma.tup11R314,
    ¬ @Equation1046 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1046) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law1046) (by native_decide) v.1 v.2
    ((@Law1046.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1082 takes them (13 nodes). -/
def ordS11R314_Law1082 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1082. -/
theorem noS11R314_Law1082 : ∀ v : Magma.tup11R314,
    ¬ @Equation1082 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1082) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law1082) (by native_decide) v.1 v.2
    ((@Law1082.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1239 takes them (13 nodes). -/
def ordS11R314_Law1239 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1239. -/
theorem noS11R314_Law1239 : ∀ v : Magma.tup11R314,
    ¬ @Equation1239 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1239) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law1239) (by native_decide) v.1 v.2
    ((@Law1239.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (14 nodes). -/
def ordS11R314_Law1242 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1242. -/
theorem noS11R314_Law1242 : ∀ v : Magma.tup11R314,
    ¬ @Equation1242 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1285 takes them (14 nodes). -/
def ordS11R314_Law1285 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1285. -/
theorem noS11R314_Law1285 : ∀ v : Magma.tup11R314,
    ¬ @Equation1285 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1285) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law1285) (by native_decide) v.1 v.2
    ((@Law1285.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1312 takes them (12 nodes). -/
def ordS11R314_Law1312 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1312. -/
theorem noS11R314_Law1312 : ∀ v : Magma.tup11R314,
    ¬ @Equation1312 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1312) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law1312) (by native_decide) v.1 v.2
    ((@Law1312.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2241 takes them (12 nodes). -/
def ordS11R314_Law2241 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2241. -/
theorem noS11R314_Law2241 : ∀ v : Magma.tup11R314,
    ¬ @Equation2241 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2241) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2241) (by native_decide) v.1 v.2
    ((@Law2241.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2244 takes them (14 nodes). -/
def ordS11R314_Law2244 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2244. -/
theorem noS11R314_Law2244 : ∀ v : Magma.tup11R314,
    ¬ @Equation2244 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2244) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2244) (by native_decide) v.1 v.2
    ((@Law2244.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2293 takes them (13 nodes). -/
def ordS11R314_Law2293 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2293. -/
theorem noS11R314_Law2293 : ∀ v : Magma.tup11R314,
    ¬ @Equation2293 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2293) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2293) (by native_decide) v.1 v.2
    ((@Law2293.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (14 nodes). -/
def ordS11R314_Law2330 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2330. -/
theorem noS11R314_Law2330 : ∀ v : Magma.tup11R314,
    ¬ @Equation2330 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2447 takes them (13 nodes). -/
def ordS11R314_Law2447 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2447. -/
theorem noS11R314_Law2447 : ∀ v : Magma.tup11R314,
    ¬ @Equation2447 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2447) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2447) (by native_decide) v.1 v.2
    ((@Law2447.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2506 takes them (15 nodes). -/
def ordS11R314_Law2506 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2506. -/
theorem noS11R314_Law2506 : ∀ v : Magma.tup11R314,
    ¬ @Equation2506 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2506) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2506) (by native_decide) v.1 v.2
    ((@Law2506.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2853 takes them (15 nodes). -/
def ordS11R314_Law2853 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2853. -/
theorem noS11R314_Law2853 : ∀ v : Magma.tup11R314,
    ¬ @Equation2853 (Fin 11) (Magma.srch11R314 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2853) (E := S11R314.E) (tr := S11R314.tr) (z := S11R314.z)
    (st := S11R314.st) (X := S11R314.X) (envs := Magma.envsRed 11 S11R314.E 2)
    (ord := ordS11R314_Law2853) (by native_decide) v.1 v.2
    ((@Law2853.models_iff (Fin 11) (Magma.srch11R314 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch11R314_refutes_0 :
    FamilyRefutes Magma.srch11R314 [
      676, 1046, 1082, 1239, 1242, 1285, 1312, 2241, 2244, 2293, 2330, 2447, 2506, 2853
    ] :=
  ⟨noS11R314_Law676, noS11R314_Law1046, noS11R314_Law1082, noS11R314_Law1239, noS11R314_Law1242, noS11R314_Law1285, noS11R314_Law1312, noS11R314_Law2241, noS11R314_Law2244, noS11R314_Law2293, noS11R314_Law2330, noS11R314_Law2447, noS11R314_Law2506, noS11R314_Law2853⟩
