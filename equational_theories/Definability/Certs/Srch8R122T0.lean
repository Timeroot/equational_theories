import equational_theories.Definability.Srch_S8R122

/-!
# Structural certificate targets: `Magma.srch8R122`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R122_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `20` equations here, 254 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R122_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 429 takes them (15 nodes). -/
def ordS8R122_Law429 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 429. -/
theorem noS8R122_Law429 : ∀ v : Magma.tup8R122,
    ¬ @Equation429 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 622 takes them (11 nodes). -/
def ordS8R122_Law622 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 622. -/
theorem noS8R122_Law622 : ∀ v : Magma.tup8R122,
    ¬ @Equation622 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law622) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law622) (by native_decide) v.1 v.2
    ((@Law622.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 819 takes them (10 nodes). -/
def ordS8R122_Law819 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 819. -/
theorem noS8R122_Law819 : ∀ v : Magma.tup8R122,
    ¬ @Equation819 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law819) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law819) (by native_decide) v.1 v.2
    ((@Law819.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 825 takes them (12 nodes). -/
def ordS8R122_Law825 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 825. -/
theorem noS8R122_Law825 : ∀ v : Magma.tup8R122,
    ¬ @Equation825 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law825) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law825) (by native_decide) v.1 v.2
    ((@Law825.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1028 takes them (16 nodes). -/
def ordS8R122_Law1028 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1028. -/
theorem noS8R122_Law1028 : ∀ v : Magma.tup8R122,
    ¬ @Equation1028 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1028) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law1028) (by native_decide) v.1 v.2
    ((@Law1028.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1225 takes them (16 nodes). -/
def ordS8R122_Law1225 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1225. -/
theorem noS8R122_Law1225 : ∀ v : Magma.tup8R122,
    ¬ @Equation1225 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1225) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law1225) (by native_decide) v.1 v.2
    ((@Law1225.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1248 takes them (15 nodes). -/
def ordS8R122_Law1248 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1248. -/
theorem noS8R122_Law1248 : ∀ v : Magma.tup8R122,
    ¬ @Equation1248 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1248) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law1248) (by native_decide) v.1 v.2
    ((@Law1248.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2246 takes them (15 nodes). -/
def ordS8R122_Law2246 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2246. -/
theorem noS8R122_Law2246 : ∀ v : Magma.tup8R122,
    ¬ @Equation2246 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2246) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law2246) (by native_decide) v.1 v.2
    ((@Law2246.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2253 takes them (16 nodes). -/
def ordS8R122_Law2253 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2253. -/
theorem noS8R122_Law2253 : ∀ v : Magma.tup8R122,
    ¬ @Equation2253 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2253) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law2253) (by native_decide) v.1 v.2
    ((@Law2253.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2466 takes them (16 nodes). -/
def ordS8R122_Law2466 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2466. -/
theorem noS8R122_Law2466 : ∀ v : Magma.tup8R122,
    ¬ @Equation2466 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2466) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law2466) (by native_decide) v.1 v.2
    ((@Law2466.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2659 takes them (10 nodes). -/
def ordS8R122_Law2659 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2659. -/
theorem noS8R122_Law2659 : ∀ v : Magma.tup8R122,
    ¬ @Equation2659 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2659) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law2659) (by native_decide) v.1 v.2
    ((@Law2659.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2669 takes them (12 nodes). -/
def ordS8R122_Law2669 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2669. -/
theorem noS8R122_Law2669 : ∀ v : Magma.tup8R122,
    ¬ @Equation2669 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2669) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law2669) (by native_decide) v.1 v.2
    ((@Law2669.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2872 takes them (11 nodes). -/
def ordS8R122_Law2872 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2872. -/
theorem noS8R122_Law2872 : ∀ v : Magma.tup8R122,
    ¬ @Equation2872 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2872) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law2872) (by native_decide) v.1 v.2
    ((@Law2872.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (15 nodes). -/
def ordS8R122_Law3068 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3068. -/
theorem noS8R122_Law3068 : ∀ v : Magma.tup8R122,
    ¬ @Equation3068 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3509 takes them (13 nodes). -/
def ordS8R122_Law3509 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3509. -/
theorem noS8R122_Law3509 : ∀ v : Magma.tup8R122,
    ¬ @Equation3509 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3509) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law3509) (by native_decide) v.1 v.2
    ((@Law3509.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3712 takes them (9 nodes). -/
def ordS8R122_Law3712 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3712. -/
theorem noS8R122_Law3712 : ∀ v : Magma.tup8R122,
    ¬ @Equation3712 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3712) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law3712) (by native_decide) v.1 v.2
    ((@Law3712.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3725 takes them (9 nodes). -/
def ordS8R122_Law3725 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3725. -/
theorem noS8R122_Law3725 : ∀ v : Magma.tup8R122,
    ¬ @Equation3725 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3725) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law3725) (by native_decide) v.1 v.2
    ((@Law3725.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3928 takes them (13 nodes). -/
def ordS8R122_Law3928 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3928. -/
theorem noS8R122_Law3928 : ∀ v : Magma.tup8R122,
    ¬ @Equation3928 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3928) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law3928) (by native_decide) v.1 v.2
    ((@Law3928.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4396 takes them (10 nodes). -/
def ordS8R122_Law4396 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4396. -/
theorem noS8R122_Law4396 : ∀ v : Magma.tup8R122,
    ¬ @Equation4396 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4396) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law4396) (by native_decide) v.1 v.2
    ((@Law4396.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4473 takes them (10 nodes). -/
def ordS8R122_Law4473 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4473. -/
theorem noS8R122_Law4473 : ∀ v : Magma.tup8R122,
    ¬ @Equation4473 (Fin 8) (Magma.srch8R122 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4473) (E := S8R122.E) (tr := S8R122.tr) (z := S8R122.z)
    (st := S8R122.st) (X := S8R122.X) (envs := Magma.envsRed 8 S8R122.E 2)
    (ord := ordS8R122_Law4473) (by native_decide) v.1 v.2
    ((@Law4473.models_iff (Fin 8) (Magma.srch8R122 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch8R122_refutes_0 :
    FamilyRefutes Magma.srch8R122 [
      429, 622, 819, 825, 1028, 1225, 1248, 2246, 2253, 2466, 2659, 2669, 2872, 3068, 3509, 3712,
      3725, 3928, 4396, 4473
    ] :=
  ⟨noS8R122_Law429, noS8R122_Law622, noS8R122_Law819, noS8R122_Law825, noS8R122_Law1028, noS8R122_Law1225, noS8R122_Law1248, noS8R122_Law2246, noS8R122_Law2253, noS8R122_Law2466, noS8R122_Law2659, noS8R122_Law2669, noS8R122_Law2872, noS8R122_Law3068, noS8R122_Law3509, noS8R122_Law3712, noS8R122_Law3725, noS8R122_Law3928, noS8R122_Law4396, noS8R122_Law4473⟩
