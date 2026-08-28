import equational_theories.Definability.Srch_S9R205

/-!
# Structural certificate targets: `Magma.srch9R205` (part 1 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R205_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 354 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R205_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 16 takes them (4 nodes). -/
def ordS9R205_Law16 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 16. -/
theorem noS9R205_Law16 : ∀ v : Magma.tup9R205,
    ¬ @Equation16 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (4 nodes). -/
def ordS9R205_Law26 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 26. -/
theorem noS9R205_Law26 : ∀ v : Magma.tup9R205,
    ¬ @Equation26 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 53 takes them (4 nodes). -/
def ordS9R205_Law53 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 53. -/
theorem noS9R205_Law53 : ∀ v : Magma.tup9R205,
    ¬ @Equation53 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law53) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law53) (by native_decide) v.1 v.2
    ((@Law53.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 55 takes them (5 nodes). -/
def ordS9R205_Law55 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 55. -/
theorem noS9R205_Law55 : ∀ v : Magma.tup9R205,
    ¬ @Equation55 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law55) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law55) (by native_decide) v.1 v.2
    ((@Law55.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 72 takes them (4 nodes). -/
def ordS9R205_Law72 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 72. -/
theorem noS9R205_Law72 : ∀ v : Magma.tup9R205,
    ¬ @Equation72 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law72) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law72) (by native_decide) v.1 v.2
    ((@Law72.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 75 takes them (3 nodes). -/
def ordS9R205_Law75 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 75. -/
theorem noS9R205_Law75 : ∀ v : Magma.tup9R205,
    ¬ @Equation75 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law75) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law75) (by native_decide) v.1 v.2
    ((@Law75.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 102 takes them (4 nodes). -/
def ordS9R205_Law102 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 102. -/
theorem noS9R205_Law102 : ∀ v : Magma.tup9R205,
    ¬ @Equation102 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law102) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law102) (by native_decide) v.1 v.2
    ((@Law102.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 105 takes them (4 nodes). -/
def ordS9R205_Law105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 105. -/
theorem noS9R205_Law105 : ∀ v : Magma.tup9R205,
    ¬ @Equation105 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law105) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law105) (by native_decide) v.1 v.2
    ((@Law105.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 127 takes them (4 nodes). -/
def ordS9R205_Law127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 127. -/
theorem noS9R205_Law127 : ∀ v : Magma.tup9R205,
    ¬ @Equation127 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 159 takes them (4 nodes). -/
def ordS9R205_Law159 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 159. -/
theorem noS9R205_Law159 : ∀ v : Magma.tup9R205,
    ¬ @Equation159 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law159) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law159) (by native_decide) v.1 v.2
    ((@Law159.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (4 nodes). -/
def ordS9R205_Law160 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 160. -/
theorem noS9R205_Law160 : ∀ v : Magma.tup9R205,
    ¬ @Equation160 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (4 nodes). -/
def ordS9R205_Law179 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 179. -/
theorem noS9R205_Law179 : ∀ v : Magma.tup9R205,
    ¬ @Equation179 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (4 nodes). -/
def ordS9R205_Law212 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 212. -/
theorem noS9R205_Law212 : ∀ v : Magma.tup9R205,
    ¬ @Equation212 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 221 takes them (4 nodes). -/
def ordS9R205_Law221 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 221. -/
theorem noS9R205_Law221 : ∀ v : Magma.tup9R205,
    ¬ @Equation221 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law221) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law221) (by native_decide) v.1 v.2
    ((@Law221.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 228 takes them (4 nodes). -/
def ordS9R205_Law228 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 228. -/
theorem noS9R205_Law228 : ∀ v : Magma.tup9R205,
    ¬ @Equation228 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law228) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law228) (by native_decide) v.1 v.2
    ((@Law228.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 258 takes them (4 nodes). -/
def ordS9R205_Law258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 258. -/
theorem noS9R205_Law258 : ∀ v : Magma.tup9R205,
    ¬ @Equation258 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law258) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law258) (by native_decide) v.1 v.2
    ((@Law258.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 263 takes them (5 nodes). -/
def ordS9R205_Law263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 263. -/
theorem noS9R205_Law263 : ∀ v : Magma.tup9R205,
    ¬ @Equation263 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law263) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law263) (by native_decide) v.1 v.2
    ((@Law263.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 264 takes them (3 nodes). -/
def ordS9R205_Law264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 264. -/
theorem noS9R205_Law264 : ∀ v : Magma.tup9R205,
    ¬ @Equation264 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law264) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law264) (by native_decide) v.1 v.2
    ((@Law264.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 273 takes them (4 nodes). -/
def ordS9R205_Law273 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 273. -/
theorem noS9R205_Law273 : ∀ v : Magma.tup9R205,
    ¬ @Equation273 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law273) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law273) (by native_decide) v.1 v.2
    ((@Law273.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 315 takes them (4 nodes). -/
def ordS9R205_Law315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 315. -/
theorem noS9R205_Law315 : ∀ v : Magma.tup9R205,
    ¬ @Equation315 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law315) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law315) (by native_decide) v.1 v.2
    ((@Law315.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 362 takes them (4 nodes). -/
def ordS9R205_Law362 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 362. -/
theorem noS9R205_Law362 : ∀ v : Magma.tup9R205,
    ¬ @Equation362 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law362) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law362) (by native_decide) v.1 v.2
    ((@Law362.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 417 takes them (4 nodes). -/
def ordS9R205_Law417 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 417. -/
theorem noS9R205_Law417 : ∀ v : Magma.tup9R205,
    ¬ @Equation417 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 419 takes them (5 nodes). -/
def ordS9R205_Law419 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 419. -/
theorem noS9R205_Law419 : ∀ v : Magma.tup9R205,
    ¬ @Equation419 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 427 takes them (3 nodes). -/
def ordS9R205_Law427 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 427. -/
theorem noS9R205_Law427 : ∀ v : Magma.tup9R205,
    ¬ @Equation427 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 429 takes them (4 nodes). -/
def ordS9R205_Law429 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 429. -/
theorem noS9R205_Law429 : ∀ v : Magma.tup9R205,
    ¬ @Equation429 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 430 takes them (4 nodes). -/
def ordS9R205_Law430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 430. -/
theorem noS9R205_Law430 : ∀ v : Magma.tup9R205,
    ¬ @Equation430 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 436 takes them (5 nodes). -/
def ordS9R205_Law436 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 436. -/
theorem noS9R205_Law436 : ∀ v : Magma.tup9R205,
    ¬ @Equation436 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law436) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law436) (by native_decide) v.1 v.2
    ((@Law436.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 437 takes them (3 nodes). -/
def ordS9R205_Law437 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 437. -/
theorem noS9R205_Law437 : ∀ v : Magma.tup9R205,
    ¬ @Equation437 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law437) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law437) (by native_decide) v.1 v.2
    ((@Law437.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 439 takes them (4 nodes). -/
def ordS9R205_Law439 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 439. -/
theorem noS9R205_Law439 : ∀ v : Magma.tup9R205,
    ¬ @Equation439 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law439) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law439) (by native_decide) v.1 v.2
    ((@Law439.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (4 nodes). -/
def ordS9R205_Law466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 466. -/
theorem noS9R205_Law466 : ∀ v : Magma.tup9R205,
    ¬ @Equation466 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 473 takes them (3 nodes). -/
def ordS9R205_Law473 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 473. -/
theorem noS9R205_Law473 : ∀ v : Magma.tup9R205,
    ¬ @Equation473 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (4 nodes). -/
def ordS9R205_Law500 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 500. -/
theorem noS9R205_Law500 : ∀ v : Magma.tup9R205,
    ¬ @Equation500 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 510 takes them (3 nodes). -/
def ordS9R205_Law510 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 510. -/
theorem noS9R205_Law510 : ∀ v : Magma.tup9R205,
    ¬ @Equation510 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law510) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law510) (by native_decide) v.1 v.2
    ((@Law510.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (4 nodes). -/
def ordS9R205_Law528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 528. -/
theorem noS9R205_Law528 : ∀ v : Magma.tup9R205,
    ¬ @Equation528 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 562 takes them (3 nodes). -/
def ordS9R205_Law562 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 562. -/
theorem noS9R205_Law562 : ∀ v : Magma.tup9R205,
    ¬ @Equation562 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (4 nodes). -/
def ordS9R205_Law575 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 575. -/
theorem noS9R205_Law575 : ∀ v : Magma.tup9R205,
    ¬ @Equation575 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 617 takes them (4 nodes). -/
def ordS9R205_Law617 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 617. -/
theorem noS9R205_Law617 : ∀ v : Magma.tup9R205,
    ¬ @Equation617 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law617) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law617) (by native_decide) v.1 v.2
    ((@Law617.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (4 nodes). -/
def ordS9R205_Law620 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 620. -/
theorem noS9R205_Law620 : ∀ v : Magma.tup9R205,
    ¬ @Equation620 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 630 takes them (4 nodes). -/
def ordS9R205_Law630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 630. -/
theorem noS9R205_Law630 : ∀ v : Magma.tup9R205,
    ¬ @Equation630 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law630) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law630) (by native_decide) v.1 v.2
    ((@Law630.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 639 takes them (4 nodes). -/
def ordS9R205_Law639 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 639. -/
theorem noS9R205_Law639 : ∀ v : Magma.tup9R205,
    ¬ @Equation639 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law639) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law639) (by native_decide) v.1 v.2
    ((@Law639.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 642 takes them (5 nodes). -/
def ordS9R205_Law642 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 642. -/
theorem noS9R205_Law642 : ∀ v : Magma.tup9R205,
    ¬ @Equation642 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law642) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law642) (by native_decide) v.1 v.2
    ((@Law642.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 669 takes them (4 nodes). -/
def ordS9R205_Law669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 669. -/
theorem noS9R205_Law669 : ∀ v : Magma.tup9R205,
    ¬ @Equation669 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law669) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law669) (by native_decide) v.1 v.2
    ((@Law669.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 679 takes them (3 nodes). -/
def ordS9R205_Law679 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 679. -/
theorem noS9R205_Law679 : ∀ v : Magma.tup9R205,
    ¬ @Equation679 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law679) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law679) (by native_decide) v.1 v.2
    ((@Law679.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 703 takes them (4 nodes). -/
def ordS9R205_Law703 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 703. -/
theorem noS9R205_Law703 : ∀ v : Magma.tup9R205,
    ¬ @Equation703 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law703) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law703) (by native_decide) v.1 v.2
    ((@Law703.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 716 takes them (3 nodes). -/
def ordS9R205_Law716 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 716. -/
theorem noS9R205_Law716 : ∀ v : Magma.tup9R205,
    ¬ @Equation716 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 825 takes them (4 nodes). -/
def ordS9R205_Law825 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 825. -/
theorem noS9R205_Law825 : ∀ v : Magma.tup9R205,
    ¬ @Equation825 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law825) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law825) (by native_decide) v.1 v.2
    ((@Law825.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 826 takes them (4 nodes). -/
def ordS9R205_Law826 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 826. -/
theorem noS9R205_Law826 : ∀ v : Magma.tup9R205,
    ¬ @Equation826 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law826) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law826) (by native_decide) v.1 v.2
    ((@Law826.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 836 takes them (4 nodes). -/
def ordS9R205_Law836 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 836. -/
theorem noS9R205_Law836 : ∀ v : Magma.tup9R205,
    ¬ @Equation836 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (4 nodes). -/
def ordS9R205_Law843 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 843. -/
theorem noS9R205_Law843 : ∀ v : Magma.tup9R205,
    ¬ @Equation843 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 845 takes them (5 nodes). -/
def ordS9R205_Law845 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 845. -/
theorem noS9R205_Law845 : ∀ v : Magma.tup9R205,
    ¬ @Equation845 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law845) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law845) (by native_decide) v.1 v.2
    ((@Law845.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 872 takes them (3 nodes). -/
def ordS9R205_Law872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 872. -/
theorem noS9R205_Law872 : ∀ v : Magma.tup9R205,
    ¬ @Equation872 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law872) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law872) (by native_decide) v.1 v.2
    ((@Law872.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 906 takes them (3 nodes). -/
def ordS9R205_Law906 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 906. -/
theorem noS9R205_Law906 : ∀ v : Magma.tup9R205,
    ¬ @Equation906 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law906) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law906) (by native_decide) v.1 v.2
    ((@Law906.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 909 takes them (4 nodes). -/
def ordS9R205_Law909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 909. -/
theorem noS9R205_Law909 : ∀ v : Magma.tup9R205,
    ¬ @Equation909 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law909) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law909) (by native_decide) v.1 v.2
    ((@Law909.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 916 takes them (4 nodes). -/
def ordS9R205_Law916 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 916. -/
theorem noS9R205_Law916 : ∀ v : Magma.tup9R205,
    ¬ @Equation916 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law916) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law916) (by native_decide) v.1 v.2
    ((@Law916.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (3 nodes). -/
def ordS9R205_Law919 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 919. -/
theorem noS9R205_Law919 : ∀ v : Magma.tup9R205,
    ¬ @Equation919 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (3 nodes). -/
def ordS9R205_Law1023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1023. -/
theorem noS9R205_Law1023 : ∀ v : Magma.tup9R205,
    ¬ @Equation1023 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1029 takes them (4 nodes). -/
def ordS9R205_Law1029 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1029. -/
theorem noS9R205_Law1029 : ∀ v : Magma.tup9R205,
    ¬ @Equation1029 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1029) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1029) (by native_decide) v.1 v.2
    ((@Law1029.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (4 nodes). -/
def ordS9R205_Law1036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1036. -/
theorem noS9R205_Law1036 : ∀ v : Magma.tup9R205,
    ¬ @Equation1036 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1038 takes them (5 nodes). -/
def ordS9R205_Law1038 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1038. -/
theorem noS9R205_Law1038 : ∀ v : Magma.tup9R205,
    ¬ @Equation1038 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1038) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1038) (by native_decide) v.1 v.2
    ((@Law1038.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1039 takes them (3 nodes). -/
def ordS9R205_Law1039 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1039. -/
theorem noS9R205_Law1039 : ∀ v : Magma.tup9R205,
    ¬ @Equation1039 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1039) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1039) (by native_decide) v.1 v.2
    ((@Law1039.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1045 takes them (5 nodes). -/
def ordS9R205_Law1045 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1045. -/
theorem noS9R205_Law1045 : ∀ v : Magma.tup9R205,
    ¬ @Equation1045 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1046 takes them (3 nodes). -/
def ordS9R205_Law1046 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1046. -/
theorem noS9R205_Law1046 : ∀ v : Magma.tup9R205,
    ¬ @Equation1046 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1046) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1046) (by native_decide) v.1 v.2
    ((@Law1046.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (4 nodes). -/
def ordS9R205_Law1075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1075. -/
theorem noS9R205_Law1075 : ∀ v : Magma.tup9R205,
    ¬ @Equation1075 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (3 nodes). -/
def ordS9R205_Law1109 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1109. -/
theorem noS9R205_Law1109 : ∀ v : Magma.tup9R205,
    ¬ @Equation1109 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1113 takes them (3 nodes). -/
def ordS9R205_Law1113 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1113. -/
theorem noS9R205_Law1113 : ∀ v : Magma.tup9R205,
    ¬ @Equation1113 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1113) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1113) (by native_decide) v.1 v.2
    ((@Law1113.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (4 nodes). -/
def ordS9R205_Law1122 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1122. -/
theorem noS9R205_Law1122 : ∀ v : Magma.tup9R205,
    ¬ @Equation1122 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (4 nodes). -/
def ordS9R205_Law1184 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1184. -/
theorem noS9R205_Law1184 : ∀ v : Magma.tup9R205,
    ¬ @Equation1184 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1226 takes them (4 nodes). -/
def ordS9R205_Law1226 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1226. -/
theorem noS9R205_Law1226 : ∀ v : Magma.tup9R205,
    ¬ @Equation1226 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1226) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1226) (by native_decide) v.1 v.2
    ((@Law1226.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1229 takes them (3 nodes). -/
def ordS9R205_Law1229 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1229. -/
theorem noS9R205_Law1229 : ∀ v : Magma.tup9R205,
    ¬ @Equation1229 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1229) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1229) (by native_decide) v.1 v.2
    ((@Law1229.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1231 takes them (5 nodes). -/
def ordS9R205_Law1231 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1231. -/
theorem noS9R205_Law1231 : ∀ v : Magma.tup9R205,
    ¬ @Equation1231 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1231) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1231) (by native_decide) v.1 v.2
    ((@Law1231.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1232 takes them (3 nodes). -/
def ordS9R205_Law1232 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1232. -/
theorem noS9R205_Law1232 : ∀ v : Magma.tup9R205,
    ¬ @Equation1232 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1232) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1232) (by native_decide) v.1 v.2
    ((@Law1232.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1239 takes them (3 nodes). -/
def ordS9R205_Law1239 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1239. -/
theorem noS9R205_Law1239 : ∀ v : Magma.tup9R205,
    ¬ @Equation1239 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1239) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1239) (by native_decide) v.1 v.2
    ((@Law1239.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1241 takes them (5 nodes). -/
def ordS9R205_Law1241 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1241. -/
theorem noS9R205_Law1241 : ∀ v : Magma.tup9R205,
    ¬ @Equation1241 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1241) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1241) (by native_decide) v.1 v.2
    ((@Law1241.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (3 nodes). -/
def ordS9R205_Law1242 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1242. -/
theorem noS9R205_Law1242 : ∀ v : Magma.tup9R205,
    ¬ @Equation1242 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1249 takes them (4 nodes). -/
def ordS9R205_Law1249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1249. -/
theorem noS9R205_Law1249 : ∀ v : Magma.tup9R205,
    ¬ @Equation1249 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1322 takes them (3 nodes). -/
def ordS9R205_Law1322 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1322. -/
theorem noS9R205_Law1322 : ∀ v : Magma.tup9R205,
    ¬ @Equation1322 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1322) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1322) (by native_decide) v.1 v.2
    ((@Law1322.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (4 nodes). -/
def ordS9R205_Law1325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1325. -/
theorem noS9R205_Law1325 : ∀ v : Magma.tup9R205,
    ¬ @Equation1325 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1432 takes them (4 nodes). -/
def ordS9R205_Law1432 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1432. -/
theorem noS9R205_Law1432 : ∀ v : Magma.tup9R205,
    ¬ @Equation1432 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1432) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1432) (by native_decide) v.1 v.2
    ((@Law1432.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1434 takes them (5 nodes). -/
def ordS9R205_Law1434 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1434. -/
theorem noS9R205_Law1434 : ∀ v : Magma.tup9R205,
    ¬ @Equation1434 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1434) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1434) (by native_decide) v.1 v.2
    ((@Law1434.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (4 nodes). -/
def ordS9R205_Law1442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1442. -/
theorem noS9R205_Law1442 : ∀ v : Magma.tup9R205,
    ¬ @Equation1442 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (5 nodes). -/
def ordS9R205_Law1444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1444. -/
theorem noS9R205_Law1444 : ∀ v : Magma.tup9R205,
    ¬ @Equation1444 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1451 takes them (4 nodes). -/
def ordS9R205_Law1451 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1451. -/
theorem noS9R205_Law1451 : ∀ v : Magma.tup9R205,
    ¬ @Equation1451 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1451) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1451) (by native_decide) v.1 v.2
    ((@Law1451.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (4 nodes). -/
def ordS9R205_Law1455 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1455. -/
theorem noS9R205_Law1455 : ∀ v : Magma.tup9R205,
    ¬ @Equation1455 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (4 nodes). -/
def ordS9R205_Law1481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1481. -/
theorem noS9R205_Law1481 : ∀ v : Magma.tup9R205,
    ¬ @Equation1481 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1519 takes them (3 nodes). -/
def ordS9R205_Law1519 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1519. -/
theorem noS9R205_Law1519 : ∀ v : Magma.tup9R205,
    ¬ @Equation1519 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1519) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1519) (by native_decide) v.1 v.2
    ((@Law1519.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1525 takes them (4 nodes). -/
def ordS9R205_Law1525 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1525. -/
theorem noS9R205_Law1525 : ∀ v : Magma.tup9R205,
    ¬ @Equation1525 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1525) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1525) (by native_decide) v.1 v.2
    ((@Law1525.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (3 nodes). -/
def ordS9R205_Law1528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1528. -/
theorem noS9R205_Law1528 : ∀ v : Magma.tup9R205,
    ¬ @Equation1528 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (4 nodes). -/
def ordS9R205_Law1632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1632. -/
theorem noS9R205_Law1632 : ∀ v : Magma.tup9R205,
    ¬ @Equation1632 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (4 nodes). -/
def ordS9R205_Law1635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1635. -/
theorem noS9R205_Law1635 : ∀ v : Magma.tup9R205,
    ¬ @Equation1635 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1647 takes them (5 nodes). -/
def ordS9R205_Law1647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1647. -/
theorem noS9R205_Law1647 : ∀ v : Magma.tup9R205,
    ¬ @Equation1647 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1647) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1647) (by native_decide) v.1 v.2
    ((@Law1647.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (5 nodes). -/
def ordS9R205_Law1654 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1654. -/
theorem noS9R205_Law1654 : ∀ v : Magma.tup9R205,
    ¬ @Equation1654 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch9R205_refutes_0 :
    FamilyRefutes Magma.srch9R205 [
      16, 26, 53, 55, 72, 75, 102, 105, 127, 159, 160, 179, 212, 221, 228, 258, 263, 264, 273,
      315, 362, 417, 419, 427, 429, 430, 436, 437, 439, 466, 473, 500, 510, 528, 562, 575, 617,
      620, 630, 639, 642, 669, 679, 703, 716, 825, 826, 836, 843, 845, 872, 906, 909, 916, 919,
      1023, 1029, 1036, 1038, 1039, 1045, 1046, 1075, 1109, 1113, 1122, 1184, 1226, 1229, 1231,
      1232, 1239, 1241, 1242, 1249, 1322, 1325, 1432, 1434, 1442, 1444, 1451, 1455, 1481, 1519,
      1525, 1528, 1632, 1635, 1647, 1654
    ] :=
  ⟨noS9R205_Law16, noS9R205_Law26, noS9R205_Law53, noS9R205_Law55, noS9R205_Law72, noS9R205_Law75, noS9R205_Law102, noS9R205_Law105, noS9R205_Law127, noS9R205_Law159, noS9R205_Law160, noS9R205_Law179, noS9R205_Law212, noS9R205_Law221, noS9R205_Law228, noS9R205_Law258, noS9R205_Law263, noS9R205_Law264, noS9R205_Law273, noS9R205_Law315, noS9R205_Law362, noS9R205_Law417, noS9R205_Law419, noS9R205_Law427, noS9R205_Law429, noS9R205_Law430, noS9R205_Law436, noS9R205_Law437, noS9R205_Law439, noS9R205_Law466, noS9R205_Law473, noS9R205_Law500, noS9R205_Law510, noS9R205_Law528, noS9R205_Law562, noS9R205_Law575, noS9R205_Law617, noS9R205_Law620, noS9R205_Law630, noS9R205_Law639, noS9R205_Law642, noS9R205_Law669, noS9R205_Law679, noS9R205_Law703, noS9R205_Law716, noS9R205_Law825, noS9R205_Law826, noS9R205_Law836, noS9R205_Law843, noS9R205_Law845, noS9R205_Law872, noS9R205_Law906, noS9R205_Law909, noS9R205_Law916, noS9R205_Law919, noS9R205_Law1023, noS9R205_Law1029, noS9R205_Law1036, noS9R205_Law1038, noS9R205_Law1039, noS9R205_Law1045, noS9R205_Law1046, noS9R205_Law1075, noS9R205_Law1109, noS9R205_Law1113, noS9R205_Law1122, noS9R205_Law1184, noS9R205_Law1226, noS9R205_Law1229, noS9R205_Law1231, noS9R205_Law1232, noS9R205_Law1239, noS9R205_Law1241, noS9R205_Law1242, noS9R205_Law1249, noS9R205_Law1322, noS9R205_Law1325, noS9R205_Law1432, noS9R205_Law1434, noS9R205_Law1442, noS9R205_Law1444, noS9R205_Law1451, noS9R205_Law1455, noS9R205_Law1481, noS9R205_Law1519, noS9R205_Law1525, noS9R205_Law1528, noS9R205_Law1632, noS9R205_Law1635, noS9R205_Law1647, noS9R205_Law1654⟩
