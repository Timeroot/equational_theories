import equational_theories.Definability.Srch_S9R174

/-!
# Structural certificate targets: `Magma.srch9R174`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R174_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `16` equations here, 136 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R174_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1442 takes them (11 nodes). -/
def ordS9R174_Law1442 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1442. -/
theorem noS9R174_Law1442 : ∀ v : Magma.tup9R174,
    ¬ @Equation1442 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (9 nodes). -/
def ordS9R174_Law1481 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1481. -/
theorem noS9R174_Law1481 : ∀ v : Magma.tup9R174,
    ¬ @Equation1481 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (7 nodes). -/
def ordS9R174_Law1684 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1684. -/
theorem noS9R174_Law1684 : ∀ v : Magma.tup9R174,
    ¬ @Equation1684 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (7 nodes). -/
def ordS9R174_Law1848 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1848. -/
theorem noS9R174_Law1848 : ∀ v : Magma.tup9R174,
    ¬ @Equation1848 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (9 nodes). -/
def ordS9R174_Law2051 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2051. -/
theorem noS9R174_Law2051 : ∀ v : Magma.tup9R174,
    ¬ @Equation2051 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (11 nodes). -/
def ordS9R174_Law2090 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2090. -/
theorem noS9R174_Law2090 : ∀ v : Magma.tup9R174,
    ¬ @Equation2090 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (9 nodes). -/
def ordS9R174_Law3308 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3308. -/
theorem noS9R174_Law3308 : ∀ v : Magma.tup9R174,
    ¬ @Equation3308 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (6 nodes). -/
def ordS9R174_Law3331 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3331. -/
theorem noS9R174_Law3331 : ∀ v : Magma.tup9R174,
    ¬ @Equation3331 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 3)
    (ord := ordS9R174_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (11 nodes). -/
def ordS9R174_Law3511 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3511. -/
theorem noS9R174_Law3511 : ∀ v : Magma.tup9R174,
    ¬ @Equation3511 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (6 nodes). -/
def ordS9R174_Law3534 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3534. -/
theorem noS9R174_Law3534 : ∀ v : Magma.tup9R174,
    ¬ @Equation3534 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 3)
    (ord := ordS9R174_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (9 nodes). -/
def ordS9R174_Law3549 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3549. -/
theorem noS9R174_Law3549 : ∀ v : Magma.tup9R174,
    ¬ @Equation3549 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (9 nodes). -/
def ordS9R174_Law3917 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3917. -/
theorem noS9R174_Law3917 : ∀ v : Magma.tup9R174,
    ¬ @Equation3917 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (11 nodes). -/
def ordS9R174_Law3955 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3955. -/
theorem noS9R174_Law3955 : ∀ v : Magma.tup9R174,
    ¬ @Equation3955 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (6 nodes). -/
def ordS9R174_Law3997 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3997. -/
theorem noS9R174_Law3997 : ∀ v : Magma.tup9R174,
    ¬ @Equation3997 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 3)
    (ord := ordS9R174_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (9 nodes). -/
def ordS9R174_Law4158 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4158. -/
theorem noS9R174_Law4158 : ∀ v : Magma.tup9R174,
    ¬ @Equation4158 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 2)
    (ord := ordS9R174_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (6 nodes). -/
def ordS9R174_Law4200 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4200. -/
theorem noS9R174_Law4200 : ∀ v : Magma.tup9R174,
    ¬ @Equation4200 (Fin 9) (Magma.srch9R174 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S9R174.E) (tr := S9R174.tr) (z := S9R174.z)
    (st := S9R174.st) (X := S9R174.X) (envs := Magma.envsRed 9 S9R174.E 3)
    (ord := ordS9R174_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 9) (Magma.srch9R174 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch9R174_refutes_0 :
    FamilyRefutes Magma.srch9R174 [
      1442, 1481, 1684, 1848, 2051, 2090, 3308, 3331, 3511, 3534, 3549, 3917, 3955, 3997, 4158,
      4200
    ] :=
  ⟨noS9R174_Law1442, noS9R174_Law1481, noS9R174_Law1684, noS9R174_Law1848, noS9R174_Law2051, noS9R174_Law2090, noS9R174_Law3308, noS9R174_Law3331, noS9R174_Law3511, noS9R174_Law3534, noS9R174_Law3549, noS9R174_Law3917, noS9R174_Law3955, noS9R174_Law3997, noS9R174_Law4158, noS9R174_Law4200⟩
