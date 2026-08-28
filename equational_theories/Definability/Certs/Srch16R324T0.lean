import equational_theories.Definability.Srch_S16R324

/-!
# Structural certificate targets: `Magma.srch16R324` (part 1 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S16R324_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 346 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S16R324_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 16 takes them (3 nodes). -/
def ordS16R324_Law16 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 16. -/
theorem noS16R324_Law16 : ∀ v : Magma.tup16R324,
    ¬ @Equation16 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (3 nodes). -/
def ordS16R324_Law26 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 26. -/
theorem noS16R324_Law26 : ∀ v : Magma.tup16R324,
    ¬ @Equation26 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 53 takes them (5 nodes). -/
def ordS16R324_Law53 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 53. -/
theorem noS16R324_Law53 : ∀ v : Magma.tup16R324,
    ¬ @Equation53 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law53) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law53) (by native_decide) v.1 v.2
    ((@Law53.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 55 takes them (4 nodes). -/
def ordS16R324_Law55 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 55. -/
theorem noS16R324_Law55 : ∀ v : Magma.tup16R324,
    ¬ @Equation55 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law55) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law55) (by native_decide) v.1 v.2
    ((@Law55.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 65 takes them (3 nodes). -/
def ordS16R324_Law65 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 65. -/
theorem noS16R324_Law65 : ∀ v : Magma.tup16R324,
    ¬ @Equation65 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law65) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law65) (by native_decide) v.1 v.2
    ((@Law65.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 72 takes them (3 nodes). -/
def ordS16R324_Law72 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 72. -/
theorem noS16R324_Law72 : ∀ v : Magma.tup16R324,
    ¬ @Equation72 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law72) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law72) (by native_decide) v.1 v.2
    ((@Law72.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 75 takes them (5 nodes). -/
def ordS16R324_Law75 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 75. -/
theorem noS16R324_Law75 : ∀ v : Magma.tup16R324,
    ¬ @Equation75 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law75) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law75) (by native_decide) v.1 v.2
    ((@Law75.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 102 takes them (3 nodes). -/
def ordS16R324_Law102 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 102. -/
theorem noS16R324_Law102 : ∀ v : Magma.tup16R324,
    ¬ @Equation102 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law102) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law102) (by native_decide) v.1 v.2
    ((@Law102.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 105 takes them (5 nodes). -/
def ordS16R324_Law105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 105. -/
theorem noS16R324_Law105 : ∀ v : Magma.tup16R324,
    ¬ @Equation105 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law105) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law105) (by native_decide) v.1 v.2
    ((@Law105.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 117 takes them (3 nodes). -/
def ordS16R324_Law117 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 117. -/
theorem noS16R324_Law117 : ∀ v : Magma.tup16R324,
    ¬ @Equation117 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law117) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law117) (by native_decide) v.1 v.2
    ((@Law117.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 124 takes them (5 nodes). -/
def ordS16R324_Law124 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 124. -/
theorem noS16R324_Law124 : ∀ v : Magma.tup16R324,
    ¬ @Equation124 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law124) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law124) (by native_decide) v.1 v.2
    ((@Law124.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 127 takes them (3 nodes). -/
def ordS16R324_Law127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 127. -/
theorem noS16R324_Law127 : ∀ v : Magma.tup16R324,
    ¬ @Equation127 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (3 nodes). -/
def ordS16R324_Law160 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 160. -/
theorem noS16R324_Law160 : ∀ v : Magma.tup16R324,
    ¬ @Equation160 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (3 nodes). -/
def ordS16R324_Law179 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 179. -/
theorem noS16R324_Law179 : ∀ v : Magma.tup16R324,
    ¬ @Equation179 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 206 takes them (5 nodes). -/
def ordS16R324_Law206 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 206. -/
theorem noS16R324_Law206 : ∀ v : Magma.tup16R324,
    ¬ @Equation206 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law206) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law206) (by native_decide) v.1 v.2
    ((@Law206.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 209 takes them (3 nodes). -/
def ordS16R324_Law209 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 209. -/
theorem noS16R324_Law209 : ∀ v : Magma.tup16R324,
    ¬ @Equation209 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law209) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law209) (by native_decide) v.1 v.2
    ((@Law209.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (3 nodes). -/
def ordS16R324_Law212 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 212. -/
theorem noS16R324_Law212 : ∀ v : Magma.tup16R324,
    ¬ @Equation212 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 221 takes them (5 nodes). -/
def ordS16R324_Law221 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 221. -/
theorem noS16R324_Law221 : ∀ v : Magma.tup16R324,
    ¬ @Equation221 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law221) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law221) (by native_decide) v.1 v.2
    ((@Law221.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 228 takes them (3 nodes). -/
def ordS16R324_Law228 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 228. -/
theorem noS16R324_Law228 : ∀ v : Magma.tup16R324,
    ¬ @Equation228 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law228) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law228) (by native_decide) v.1 v.2
    ((@Law228.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 258 takes them (3 nodes). -/
def ordS16R324_Law258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 258. -/
theorem noS16R324_Law258 : ∀ v : Magma.tup16R324,
    ¬ @Equation258 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law258) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law258) (by native_decide) v.1 v.2
    ((@Law258.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 261 takes them (3 nodes). -/
def ordS16R324_Law261 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 261. -/
theorem noS16R324_Law261 : ∀ v : Magma.tup16R324,
    ¬ @Equation261 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law261) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law261) (by native_decide) v.1 v.2
    ((@Law261.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 263 takes them (4 nodes). -/
def ordS16R324_Law263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 263. -/
theorem noS16R324_Law263 : ∀ v : Magma.tup16R324,
    ¬ @Equation263 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law263) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law263) (by native_decide) v.1 v.2
    ((@Law263.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 264 takes them (5 nodes). -/
def ordS16R324_Law264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 264. -/
theorem noS16R324_Law264 : ∀ v : Magma.tup16R324,
    ¬ @Equation264 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law264) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law264) (by native_decide) v.1 v.2
    ((@Law264.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 273 takes them (5 nodes). -/
def ordS16R324_Law273 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 273. -/
theorem noS16R324_Law273 : ∀ v : Magma.tup16R324,
    ¬ @Equation273 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law273) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law273) (by native_decide) v.1 v.2
    ((@Law273.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 313 takes them (4 nodes). -/
def ordS16R324_Law313 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 313. -/
theorem noS16R324_Law313 : ∀ v : Magma.tup16R324,
    ¬ @Equation313 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law313) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law313) (by native_decide) v.1 v.2
    ((@Law313.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 315 takes them (3 nodes). -/
def ordS16R324_Law315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 315. -/
theorem noS16R324_Law315 : ∀ v : Magma.tup16R324,
    ¬ @Equation315 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law315) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law315) (by native_decide) v.1 v.2
    ((@Law315.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 335 takes them (4 nodes). -/
def ordS16R324_Law335 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 335. -/
theorem noS16R324_Law335 : ∀ v : Magma.tup16R324,
    ¬ @Equation335 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law335) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law335) (by native_decide) v.1 v.2
    ((@Law335.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 362 takes them (3 nodes). -/
def ordS16R324_Law362 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 362. -/
theorem noS16R324_Law362 : ∀ v : Magma.tup16R324,
    ¬ @Equation362 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law362) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law362) (by native_decide) v.1 v.2
    ((@Law362.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 365 takes them (4 nodes). -/
def ordS16R324_Law365 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 365. -/
theorem noS16R324_Law365 : ∀ v : Magma.tup16R324,
    ¬ @Equation365 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law365) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law365) (by native_decide) v.1 v.2
    ((@Law365.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 384 takes them (4 nodes). -/
def ordS16R324_Law384 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 384. -/
theorem noS16R324_Law384 : ∀ v : Magma.tup16R324,
    ¬ @Equation384 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law384) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law384) (by native_decide) v.1 v.2
    ((@Law384.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 417 takes them (5 nodes). -/
def ordS16R324_Law417 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 417. -/
theorem noS16R324_Law417 : ∀ v : Magma.tup16R324,
    ¬ @Equation417 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 419 takes them (4 nodes). -/
def ordS16R324_Law419 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 419. -/
theorem noS16R324_Law419 : ∀ v : Magma.tup16R324,
    ¬ @Equation419 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 427 takes them (3 nodes). -/
def ordS16R324_Law427 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 427. -/
theorem noS16R324_Law427 : ∀ v : Magma.tup16R324,
    ¬ @Equation427 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 429 takes them (4 nodes). -/
def ordS16R324_Law429 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 429. -/
theorem noS16R324_Law429 : ∀ v : Magma.tup16R324,
    ¬ @Equation429 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 430 takes them (5 nodes). -/
def ordS16R324_Law430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 430. -/
theorem noS16R324_Law430 : ∀ v : Magma.tup16R324,
    ¬ @Equation430 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 436 takes them (4 nodes). -/
def ordS16R324_Law436 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 436. -/
theorem noS16R324_Law436 : ∀ v : Magma.tup16R324,
    ¬ @Equation436 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law436) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law436) (by native_decide) v.1 v.2
    ((@Law436.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 437 takes them (3 nodes). -/
def ordS16R324_Law437 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 437. -/
theorem noS16R324_Law437 : ∀ v : Magma.tup16R324,
    ¬ @Equation437 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law437) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law437) (by native_decide) v.1 v.2
    ((@Law437.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 439 takes them (6 nodes). -/
def ordS16R324_Law439 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 439. -/
theorem noS16R324_Law439 : ∀ v : Magma.tup16R324,
    ¬ @Equation439 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law439) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law439) (by native_decide) v.1 v.2
    ((@Law439.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (5 nodes). -/
def ordS16R324_Law466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 466. -/
theorem noS16R324_Law466 : ∀ v : Magma.tup16R324,
    ¬ @Equation466 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 473 takes them (3 nodes). -/
def ordS16R324_Law473 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 473. -/
theorem noS16R324_Law473 : ∀ v : Magma.tup16R324,
    ¬ @Equation473 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 476 takes them (3 nodes). -/
def ordS16R324_Law476 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 476. -/
theorem noS16R324_Law476 : ∀ v : Magma.tup16R324,
    ¬ @Equation476 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law476) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law476) (by native_decide) v.1 v.2
    ((@Law476.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (3 nodes). -/
def ordS16R324_Law500 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 500. -/
theorem noS16R324_Law500 : ∀ v : Magma.tup16R324,
    ¬ @Equation500 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 503 takes them (3 nodes). -/
def ordS16R324_Law503 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 503. -/
theorem noS16R324_Law503 : ∀ v : Magma.tup16R324,
    ¬ @Equation503 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law503) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law503) (by native_decide) v.1 v.2
    ((@Law503.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 510 takes them (5 nodes). -/
def ordS16R324_Law510 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 510. -/
theorem noS16R324_Law510 : ∀ v : Magma.tup16R324,
    ¬ @Equation510 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law510) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law510) (by native_decide) v.1 v.2
    ((@Law510.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 513 takes them (3 nodes). -/
def ordS16R324_Law513 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 513. -/
theorem noS16R324_Law513 : ∀ v : Magma.tup16R324,
    ¬ @Equation513 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law513) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law513) (by native_decide) v.1 v.2
    ((@Law513.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (3 nodes). -/
def ordS16R324_Law528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 528. -/
theorem noS16R324_Law528 : ∀ v : Magma.tup16R324,
    ¬ @Equation528 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 562 takes them (3 nodes). -/
def ordS16R324_Law562 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 562. -/
theorem noS16R324_Law562 : ∀ v : Magma.tup16R324,
    ¬ @Equation562 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (3 nodes). -/
def ordS16R324_Law575 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 575. -/
theorem noS16R324_Law575 : ∀ v : Magma.tup16R324,
    ¬ @Equation575 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 617 takes them (3 nodes). -/
def ordS16R324_Law617 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 617. -/
theorem noS16R324_Law617 : ∀ v : Magma.tup16R324,
    ¬ @Equation617 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law617) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law617) (by native_decide) v.1 v.2
    ((@Law617.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (5 nodes). -/
def ordS16R324_Law620 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 620. -/
theorem noS16R324_Law620 : ∀ v : Magma.tup16R324,
    ¬ @Equation620 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 630 takes them (5 nodes). -/
def ordS16R324_Law630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 630. -/
theorem noS16R324_Law630 : ∀ v : Magma.tup16R324,
    ¬ @Equation630 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law630) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law630) (by native_decide) v.1 v.2
    ((@Law630.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 632 takes them (4 nodes). -/
def ordS16R324_Law632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 632. -/
theorem noS16R324_Law632 : ∀ v : Magma.tup16R324,
    ¬ @Equation632 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law632) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law632) (by native_decide) v.1 v.2
    ((@Law632.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 633 takes them (3 nodes). -/
def ordS16R324_Law633 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 633. -/
theorem noS16R324_Law633 : ∀ v : Magma.tup16R324,
    ¬ @Equation633 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law633) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law633) (by native_decide) v.1 v.2
    ((@Law633.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 639 takes them (6 nodes). -/
def ordS16R324_Law639 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 639. -/
theorem noS16R324_Law639 : ∀ v : Magma.tup16R324,
    ¬ @Equation639 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law639) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law639) (by native_decide) v.1 v.2
    ((@Law639.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 640 takes them (3 nodes). -/
def ordS16R324_Law640 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 640. -/
theorem noS16R324_Law640 : ∀ v : Magma.tup16R324,
    ¬ @Equation640 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law640) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law640) (by native_decide) v.1 v.2
    ((@Law640.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 642 takes them (4 nodes). -/
def ordS16R324_Law642 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 642. -/
theorem noS16R324_Law642 : ∀ v : Magma.tup16R324,
    ¬ @Equation642 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law642) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law642) (by native_decide) v.1 v.2
    ((@Law642.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 669 takes them (5 nodes). -/
def ordS16R324_Law669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 669. -/
theorem noS16R324_Law669 : ∀ v : Magma.tup16R324,
    ¬ @Equation669 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law669) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law669) (by native_decide) v.1 v.2
    ((@Law669.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 676 takes them (3 nodes). -/
def ordS16R324_Law676 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 676. -/
theorem noS16R324_Law676 : ∀ v : Magma.tup16R324,
    ¬ @Equation676 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law676) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law676) (by native_decide) v.1 v.2
    ((@Law676.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 679 takes them (3 nodes). -/
def ordS16R324_Law679 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 679. -/
theorem noS16R324_Law679 : ∀ v : Magma.tup16R324,
    ¬ @Equation679 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law679) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law679) (by native_decide) v.1 v.2
    ((@Law679.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 703 takes them (3 nodes). -/
def ordS16R324_Law703 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 703. -/
theorem noS16R324_Law703 : ∀ v : Magma.tup16R324,
    ¬ @Equation703 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law703) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law703) (by native_decide) v.1 v.2
    ((@Law703.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 707 takes them (4 nodes). -/
def ordS16R324_Law707 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 707. -/
theorem noS16R324_Law707 : ∀ v : Magma.tup16R324,
    ¬ @Equation707 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law707) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law707) (by native_decide) v.1 v.2
    ((@Law707.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 713 takes them (3 nodes). -/
def ordS16R324_Law713 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 713. -/
theorem noS16R324_Law713 : ∀ v : Magma.tup16R324,
    ¬ @Equation713 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law713) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law713) (by native_decide) v.1 v.2
    ((@Law713.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 716 takes them (5 nodes). -/
def ordS16R324_Law716 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 716. -/
theorem noS16R324_Law716 : ∀ v : Magma.tup16R324,
    ¬ @Equation716 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 826 takes them (3 nodes). -/
def ordS16R324_Law826 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 826. -/
theorem noS16R324_Law826 : ∀ v : Magma.tup16R324,
    ¬ @Equation826 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law826) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law826) (by native_decide) v.1 v.2
    ((@Law826.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 833 takes them (3 nodes). -/
def ordS16R324_Law833 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 833. -/
theorem noS16R324_Law833 : ∀ v : Magma.tup16R324,
    ¬ @Equation833 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law833) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law833) (by native_decide) v.1 v.2
    ((@Law833.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 836 takes them (5 nodes). -/
def ordS16R324_Law836 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 836. -/
theorem noS16R324_Law836 : ∀ v : Magma.tup16R324,
    ¬ @Equation836 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (5 nodes). -/
def ordS16R324_Law843 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 843. -/
theorem noS16R324_Law843 : ∀ v : Magma.tup16R324,
    ¬ @Equation843 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 845 takes them (4 nodes). -/
def ordS16R324_Law845 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 845. -/
theorem noS16R324_Law845 : ∀ v : Magma.tup16R324,
    ¬ @Equation845 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law845) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law845) (by native_decide) v.1 v.2
    ((@Law845.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 872 takes them (3 nodes). -/
def ordS16R324_Law872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 872. -/
theorem noS16R324_Law872 : ∀ v : Magma.tup16R324,
    ¬ @Equation872 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law872) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law872) (by native_decide) v.1 v.2
    ((@Law872.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 879 takes them (3 nodes). -/
def ordS16R324_Law879 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 879. -/
theorem noS16R324_Law879 : ∀ v : Magma.tup16R324,
    ¬ @Equation879 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law879) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law879) (by native_decide) v.1 v.2
    ((@Law879.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 906 takes them (5 nodes). -/
def ordS16R324_Law906 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 906. -/
theorem noS16R324_Law906 : ∀ v : Magma.tup16R324,
    ¬ @Equation906 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law906) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law906) (by native_decide) v.1 v.2
    ((@Law906.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 909 takes them (3 nodes). -/
def ordS16R324_Law909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 909. -/
theorem noS16R324_Law909 : ∀ v : Magma.tup16R324,
    ¬ @Equation909 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law909) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law909) (by native_decide) v.1 v.2
    ((@Law909.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 916 takes them (3 nodes). -/
def ordS16R324_Law916 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 916. -/
theorem noS16R324_Law916 : ∀ v : Magma.tup16R324,
    ¬ @Equation916 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law916) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law916) (by native_decide) v.1 v.2
    ((@Law916.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (5 nodes). -/
def ordS16R324_Law919 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 919. -/
theorem noS16R324_Law919 : ∀ v : Magma.tup16R324,
    ¬ @Equation919 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (5 nodes). -/
def ordS16R324_Law1023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1023. -/
theorem noS16R324_Law1023 : ∀ v : Magma.tup16R324,
    ¬ @Equation1023 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1026 takes them (3 nodes). -/
def ordS16R324_Law1026 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1026. -/
theorem noS16R324_Law1026 : ∀ v : Magma.tup16R324,
    ¬ @Equation1026 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1026) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1026) (by native_decide) v.1 v.2
    ((@Law1026.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1029 takes them (3 nodes). -/
def ordS16R324_Law1029 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1029. -/
theorem noS16R324_Law1029 : ∀ v : Magma.tup16R324,
    ¬ @Equation1029 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1029) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1029) (by native_decide) v.1 v.2
    ((@Law1029.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (5 nodes). -/
def ordS16R324_Law1036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1036. -/
theorem noS16R324_Law1036 : ∀ v : Magma.tup16R324,
    ¬ @Equation1036 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1038 takes them (6 nodes). -/
def ordS16R324_Law1038 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1038. -/
theorem noS16R324_Law1038 : ∀ v : Magma.tup16R324,
    ¬ @Equation1038 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1038) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1038) (by native_decide) v.1 v.2
    ((@Law1038.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1039 takes them (3 nodes). -/
def ordS16R324_Law1039 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1039. -/
theorem noS16R324_Law1039 : ∀ v : Magma.tup16R324,
    ¬ @Equation1039 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1039) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1039) (by native_decide) v.1 v.2
    ((@Law1039.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1045 takes them (4 nodes). -/
def ordS16R324_Law1045 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1045. -/
theorem noS16R324_Law1045 : ∀ v : Magma.tup16R324,
    ¬ @Equation1045 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1046 takes them (3 nodes). -/
def ordS16R324_Law1046 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1046. -/
theorem noS16R324_Law1046 : ∀ v : Magma.tup16R324,
    ¬ @Equation1046 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1046) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1046) (by native_decide) v.1 v.2
    ((@Law1046.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (5 nodes). -/
def ordS16R324_Law1075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1075. -/
theorem noS16R324_Law1075 : ∀ v : Magma.tup16R324,
    ¬ @Equation1075 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1082 takes them (3 nodes). -/
def ordS16R324_Law1082 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1082. -/
theorem noS16R324_Law1082 : ∀ v : Magma.tup16R324,
    ¬ @Equation1082 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1082) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1082) (by native_decide) v.1 v.2
    ((@Law1082.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1085 takes them (3 nodes). -/
def ordS16R324_Law1085 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1085. -/
theorem noS16R324_Law1085 : ∀ v : Magma.tup16R324,
    ¬ @Equation1085 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1085) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1085) (by native_decide) v.1 v.2
    ((@Law1085.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (5 nodes). -/
def ordS16R324_Law1109 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1109. -/
theorem noS16R324_Law1109 : ∀ v : Magma.tup16R324,
    ¬ @Equation1109 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1112 takes them (3 nodes). -/
def ordS16R324_Law1112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1112. -/
theorem noS16R324_Law1112 : ∀ v : Magma.tup16R324,
    ¬ @Equation1112 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1112) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1112) (by native_decide) v.1 v.2
    ((@Law1112.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1113 takes them (4 nodes). -/
def ordS16R324_Law1113 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1113. -/
theorem noS16R324_Law1113 : ∀ v : Magma.tup16R324,
    ¬ @Equation1113 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1113) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1113) (by native_decide) v.1 v.2
    ((@Law1113.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1117 takes them (4 nodes). -/
def ordS16R324_Law1117 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1117. -/
theorem noS16R324_Law1117 : ∀ v : Magma.tup16R324,
    ¬ @Equation1117 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1117) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law1117) (by native_decide) v.1 v.2
    ((@Law1117.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1119 takes them (3 nodes). -/
def ordS16R324_Law1119 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1119. -/
theorem noS16R324_Law1119 : ∀ v : Magma.tup16R324,
    ¬ @Equation1119 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1119) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1119) (by native_decide) v.1 v.2
    ((@Law1119.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (3 nodes). -/
def ordS16R324_Law1122 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1122. -/
theorem noS16R324_Law1122 : ∀ v : Magma.tup16R324,
    ¬ @Equation1122 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch16R324_refutes_0 :
    FamilyRefutes Magma.srch16R324 [
      16, 26, 53, 55, 65, 72, 75, 102, 105, 117, 124, 127, 160, 179, 206, 209, 212, 221, 228,
      258, 261, 263, 264, 273, 313, 315, 335, 362, 365, 384, 417, 419, 427, 429, 430, 436, 437,
      439, 466, 473, 476, 500, 503, 510, 513, 528, 562, 575, 617, 620, 630, 632, 633, 639, 640,
      642, 669, 676, 679, 703, 707, 713, 716, 826, 833, 836, 843, 845, 872, 879, 906, 909, 916,
      919, 1023, 1026, 1029, 1036, 1038, 1039, 1045, 1046, 1075, 1082, 1085, 1109, 1112, 1113,
      1117, 1119, 1122
    ] :=
  ⟨noS16R324_Law16, noS16R324_Law26, noS16R324_Law53, noS16R324_Law55, noS16R324_Law65, noS16R324_Law72, noS16R324_Law75, noS16R324_Law102, noS16R324_Law105, noS16R324_Law117, noS16R324_Law124, noS16R324_Law127, noS16R324_Law160, noS16R324_Law179, noS16R324_Law206, noS16R324_Law209, noS16R324_Law212, noS16R324_Law221, noS16R324_Law228, noS16R324_Law258, noS16R324_Law261, noS16R324_Law263, noS16R324_Law264, noS16R324_Law273, noS16R324_Law313, noS16R324_Law315, noS16R324_Law335, noS16R324_Law362, noS16R324_Law365, noS16R324_Law384, noS16R324_Law417, noS16R324_Law419, noS16R324_Law427, noS16R324_Law429, noS16R324_Law430, noS16R324_Law436, noS16R324_Law437, noS16R324_Law439, noS16R324_Law466, noS16R324_Law473, noS16R324_Law476, noS16R324_Law500, noS16R324_Law503, noS16R324_Law510, noS16R324_Law513, noS16R324_Law528, noS16R324_Law562, noS16R324_Law575, noS16R324_Law617, noS16R324_Law620, noS16R324_Law630, noS16R324_Law632, noS16R324_Law633, noS16R324_Law639, noS16R324_Law640, noS16R324_Law642, noS16R324_Law669, noS16R324_Law676, noS16R324_Law679, noS16R324_Law703, noS16R324_Law707, noS16R324_Law713, noS16R324_Law716, noS16R324_Law826, noS16R324_Law833, noS16R324_Law836, noS16R324_Law843, noS16R324_Law845, noS16R324_Law872, noS16R324_Law879, noS16R324_Law906, noS16R324_Law909, noS16R324_Law916, noS16R324_Law919, noS16R324_Law1023, noS16R324_Law1026, noS16R324_Law1029, noS16R324_Law1036, noS16R324_Law1038, noS16R324_Law1039, noS16R324_Law1045, noS16R324_Law1046, noS16R324_Law1075, noS16R324_Law1082, noS16R324_Law1085, noS16R324_Law1109, noS16R324_Law1112, noS16R324_Law1113, noS16R324_Law1117, noS16R324_Law1119, noS16R324_Law1122⟩
