import equational_theories.Definability.Srch_S9R322

/-!
# Structural certificate targets: `Magma.srch9R322` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R322_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `90` equations here, 379 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R322_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 16 takes them (4 nodes). -/
def ordS9R322_Law16 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 16. -/
theorem noS9R322_Law16 : ∀ v : Magma.tup9R322,
    ¬ @Equation16 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (4 nodes). -/
def ordS9R322_Law26 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 26. -/
theorem noS9R322_Law26 : ∀ v : Magma.tup9R322,
    ¬ @Equation26 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 43 takes them (3 nodes). -/
def ordS9R322_Law43 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 43. -/
theorem noS9R322_Law43 : ∀ v : Magma.tup9R322,
    ¬ @Equation43 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law43) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law43) (by native_decide) v.1 v.2
    ((@Law43.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 53 takes them (4 nodes). -/
def ordS9R322_Law53 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 53. -/
theorem noS9R322_Law53 : ∀ v : Magma.tup9R322,
    ¬ @Equation53 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law53) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law53) (by native_decide) v.1 v.2
    ((@Law53.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 55 takes them (5 nodes). -/
def ordS9R322_Law55 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 55. -/
theorem noS9R322_Law55 : ∀ v : Magma.tup9R322,
    ¬ @Equation55 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law55) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law55) (by native_decide) v.1 v.2
    ((@Law55.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 72 takes them (4 nodes). -/
def ordS9R322_Law72 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 72. -/
theorem noS9R322_Law72 : ∀ v : Magma.tup9R322,
    ¬ @Equation72 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law72) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law72) (by native_decide) v.1 v.2
    ((@Law72.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 102 takes them (4 nodes). -/
def ordS9R322_Law102 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 102. -/
theorem noS9R322_Law102 : ∀ v : Magma.tup9R322,
    ¬ @Equation102 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law102) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law102) (by native_decide) v.1 v.2
    ((@Law102.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 105 takes them (4 nodes). -/
def ordS9R322_Law105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 105. -/
theorem noS9R322_Law105 : ∀ v : Magma.tup9R322,
    ¬ @Equation105 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law105) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law105) (by native_decide) v.1 v.2
    ((@Law105.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 127 takes them (4 nodes). -/
def ordS9R322_Law127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 127. -/
theorem noS9R322_Law127 : ∀ v : Magma.tup9R322,
    ¬ @Equation127 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (4 nodes). -/
def ordS9R322_Law160 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 160. -/
theorem noS9R322_Law160 : ∀ v : Magma.tup9R322,
    ¬ @Equation160 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (4 nodes). -/
def ordS9R322_Law179 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 179. -/
theorem noS9R322_Law179 : ∀ v : Magma.tup9R322,
    ¬ @Equation179 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (4 nodes). -/
def ordS9R322_Law212 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 212. -/
theorem noS9R322_Law212 : ∀ v : Magma.tup9R322,
    ¬ @Equation212 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 221 takes them (4 nodes). -/
def ordS9R322_Law221 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 221. -/
theorem noS9R322_Law221 : ∀ v : Magma.tup9R322,
    ¬ @Equation221 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law221) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law221) (by native_decide) v.1 v.2
    ((@Law221.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 228 takes them (4 nodes). -/
def ordS9R322_Law228 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 228. -/
theorem noS9R322_Law228 : ∀ v : Magma.tup9R322,
    ¬ @Equation228 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law228) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law228) (by native_decide) v.1 v.2
    ((@Law228.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 258 takes them (4 nodes). -/
def ordS9R322_Law258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 258. -/
theorem noS9R322_Law258 : ∀ v : Magma.tup9R322,
    ¬ @Equation258 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law258) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law258) (by native_decide) v.1 v.2
    ((@Law258.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 263 takes them (5 nodes). -/
def ordS9R322_Law263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 263. -/
theorem noS9R322_Law263 : ∀ v : Magma.tup9R322,
    ¬ @Equation263 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law263) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law263) (by native_decide) v.1 v.2
    ((@Law263.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 273 takes them (4 nodes). -/
def ordS9R322_Law273 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 273. -/
theorem noS9R322_Law273 : ∀ v : Magma.tup9R322,
    ¬ @Equation273 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law273) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law273) (by native_decide) v.1 v.2
    ((@Law273.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 315 takes them (4 nodes). -/
def ordS9R322_Law315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 315. -/
theorem noS9R322_Law315 : ∀ v : Magma.tup9R322,
    ¬ @Equation315 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law315) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law315) (by native_decide) v.1 v.2
    ((@Law315.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 332 takes them (3 nodes). -/
def ordS9R322_Law332 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 332. -/
theorem noS9R322_Law332 : ∀ v : Magma.tup9R322,
    ¬ @Equation332 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law332) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law332) (by native_decide) v.1 v.2
    ((@Law332.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 362 takes them (4 nodes). -/
def ordS9R322_Law362 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 362. -/
theorem noS9R322_Law362 : ∀ v : Magma.tup9R322,
    ¬ @Equation362 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law362) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law362) (by native_decide) v.1 v.2
    ((@Law362.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 387 takes them (3 nodes). -/
def ordS9R322_Law387 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 387. -/
theorem noS9R322_Law387 : ∀ v : Magma.tup9R322,
    ¬ @Equation387 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law387) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law387) (by native_decide) v.1 v.2
    ((@Law387.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 417 takes them (4 nodes). -/
def ordS9R322_Law417 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 417. -/
theorem noS9R322_Law417 : ∀ v : Magma.tup9R322,
    ¬ @Equation417 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 419 takes them (5 nodes). -/
def ordS9R322_Law419 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 419. -/
theorem noS9R322_Law419 : ∀ v : Magma.tup9R322,
    ¬ @Equation419 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 430 takes them (4 nodes). -/
def ordS9R322_Law430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 430. -/
theorem noS9R322_Law430 : ∀ v : Magma.tup9R322,
    ¬ @Equation430 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 436 takes them (5 nodes). -/
def ordS9R322_Law436 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 436. -/
theorem noS9R322_Law436 : ∀ v : Magma.tup9R322,
    ¬ @Equation436 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law436) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law436) (by native_decide) v.1 v.2
    ((@Law436.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (4 nodes). -/
def ordS9R322_Law466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 466. -/
theorem noS9R322_Law466 : ∀ v : Magma.tup9R322,
    ¬ @Equation466 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (4 nodes). -/
def ordS9R322_Law500 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 500. -/
theorem noS9R322_Law500 : ∀ v : Magma.tup9R322,
    ¬ @Equation500 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (4 nodes). -/
def ordS9R322_Law528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 528. -/
theorem noS9R322_Law528 : ∀ v : Magma.tup9R322,
    ¬ @Equation528 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (4 nodes). -/
def ordS9R322_Law575 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 575. -/
theorem noS9R322_Law575 : ∀ v : Magma.tup9R322,
    ¬ @Equation575 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 617 takes them (4 nodes). -/
def ordS9R322_Law617 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 617. -/
theorem noS9R322_Law617 : ∀ v : Magma.tup9R322,
    ¬ @Equation617 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law617) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law617) (by native_decide) v.1 v.2
    ((@Law617.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (4 nodes). -/
def ordS9R322_Law620 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 620. -/
theorem noS9R322_Law620 : ∀ v : Magma.tup9R322,
    ¬ @Equation620 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 630 takes them (4 nodes). -/
def ordS9R322_Law630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 630. -/
theorem noS9R322_Law630 : ∀ v : Magma.tup9R322,
    ¬ @Equation630 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law630) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law630) (by native_decide) v.1 v.2
    ((@Law630.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 642 takes them (5 nodes). -/
def ordS9R322_Law642 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 642. -/
theorem noS9R322_Law642 : ∀ v : Magma.tup9R322,
    ¬ @Equation642 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law642) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law642) (by native_decide) v.1 v.2
    ((@Law642.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 669 takes them (4 nodes). -/
def ordS9R322_Law669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 669. -/
theorem noS9R322_Law669 : ∀ v : Magma.tup9R322,
    ¬ @Equation669 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law669) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law669) (by native_decide) v.1 v.2
    ((@Law669.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 703 takes them (4 nodes). -/
def ordS9R322_Law703 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 703. -/
theorem noS9R322_Law703 : ∀ v : Magma.tup9R322,
    ¬ @Equation703 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law703) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law703) (by native_decide) v.1 v.2
    ((@Law703.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 826 takes them (4 nodes). -/
def ordS9R322_Law826 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 826. -/
theorem noS9R322_Law826 : ∀ v : Magma.tup9R322,
    ¬ @Equation826 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law826) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law826) (by native_decide) v.1 v.2
    ((@Law826.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 836 takes them (4 nodes). -/
def ordS9R322_Law836 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 836. -/
theorem noS9R322_Law836 : ∀ v : Magma.tup9R322,
    ¬ @Equation836 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (4 nodes). -/
def ordS9R322_Law843 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 843. -/
theorem noS9R322_Law843 : ∀ v : Magma.tup9R322,
    ¬ @Equation843 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 845 takes them (5 nodes). -/
def ordS9R322_Law845 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 845. -/
theorem noS9R322_Law845 : ∀ v : Magma.tup9R322,
    ¬ @Equation845 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law845) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law845) (by native_decide) v.1 v.2
    ((@Law845.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 909 takes them (4 nodes). -/
def ordS9R322_Law909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 909. -/
theorem noS9R322_Law909 : ∀ v : Magma.tup9R322,
    ¬ @Equation909 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law909) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law909) (by native_decide) v.1 v.2
    ((@Law909.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 916 takes them (4 nodes). -/
def ordS9R322_Law916 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 916. -/
theorem noS9R322_Law916 : ∀ v : Magma.tup9R322,
    ¬ @Equation916 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law916) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law916) (by native_decide) v.1 v.2
    ((@Law916.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1029 takes them (4 nodes). -/
def ordS9R322_Law1029 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1029. -/
theorem noS9R322_Law1029 : ∀ v : Magma.tup9R322,
    ¬ @Equation1029 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1029) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1029) (by native_decide) v.1 v.2
    ((@Law1029.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (4 nodes). -/
def ordS9R322_Law1036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1036. -/
theorem noS9R322_Law1036 : ∀ v : Magma.tup9R322,
    ¬ @Equation1036 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1038 takes them (5 nodes). -/
def ordS9R322_Law1038 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1038. -/
theorem noS9R322_Law1038 : ∀ v : Magma.tup9R322,
    ¬ @Equation1038 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1038) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1038) (by native_decide) v.1 v.2
    ((@Law1038.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1045 takes them (5 nodes). -/
def ordS9R322_Law1045 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1045. -/
theorem noS9R322_Law1045 : ∀ v : Magma.tup9R322,
    ¬ @Equation1045 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (4 nodes). -/
def ordS9R322_Law1075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1075. -/
theorem noS9R322_Law1075 : ∀ v : Magma.tup9R322,
    ¬ @Equation1075 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (4 nodes). -/
def ordS9R322_Law1122 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1122. -/
theorem noS9R322_Law1122 : ∀ v : Magma.tup9R322,
    ¬ @Equation1122 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (4 nodes). -/
def ordS9R322_Law1184 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1184. -/
theorem noS9R322_Law1184 : ∀ v : Magma.tup9R322,
    ¬ @Equation1184 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1226 takes them (4 nodes). -/
def ordS9R322_Law1226 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1226. -/
theorem noS9R322_Law1226 : ∀ v : Magma.tup9R322,
    ¬ @Equation1226 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1226) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1226) (by native_decide) v.1 v.2
    ((@Law1226.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1231 takes them (5 nodes). -/
def ordS9R322_Law1231 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1231. -/
theorem noS9R322_Law1231 : ∀ v : Magma.tup9R322,
    ¬ @Equation1231 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1231) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1231) (by native_decide) v.1 v.2
    ((@Law1231.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1241 takes them (5 nodes). -/
def ordS9R322_Law1241 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1241. -/
theorem noS9R322_Law1241 : ∀ v : Magma.tup9R322,
    ¬ @Equation1241 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1241) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1241) (by native_decide) v.1 v.2
    ((@Law1241.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1249 takes them (4 nodes). -/
def ordS9R322_Law1249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1249. -/
theorem noS9R322_Law1249 : ∀ v : Magma.tup9R322,
    ¬ @Equation1249 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (4 nodes). -/
def ordS9R322_Law1325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1325. -/
theorem noS9R322_Law1325 : ∀ v : Magma.tup9R322,
    ¬ @Equation1325 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1432 takes them (4 nodes). -/
def ordS9R322_Law1432 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1432. -/
theorem noS9R322_Law1432 : ∀ v : Magma.tup9R322,
    ¬ @Equation1432 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1432) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1432) (by native_decide) v.1 v.2
    ((@Law1432.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1434 takes them (5 nodes). -/
def ordS9R322_Law1434 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1434. -/
theorem noS9R322_Law1434 : ∀ v : Magma.tup9R322,
    ¬ @Equation1434 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1434) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1434) (by native_decide) v.1 v.2
    ((@Law1434.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (5 nodes). -/
def ordS9R322_Law1444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1444. -/
theorem noS9R322_Law1444 : ∀ v : Magma.tup9R322,
    ¬ @Equation1444 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (4 nodes). -/
def ordS9R322_Law1455 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1455. -/
theorem noS9R322_Law1455 : ∀ v : Magma.tup9R322,
    ¬ @Equation1455 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1525 takes them (4 nodes). -/
def ordS9R322_Law1525 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1525. -/
theorem noS9R322_Law1525 : ∀ v : Magma.tup9R322,
    ¬ @Equation1525 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1525) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1525) (by native_decide) v.1 v.2
    ((@Law1525.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (4 nodes). -/
def ordS9R322_Law1632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1632. -/
theorem noS9R322_Law1632 : ∀ v : Magma.tup9R322,
    ¬ @Equation1632 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (4 nodes). -/
def ordS9R322_Law1635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1635. -/
theorem noS9R322_Law1635 : ∀ v : Magma.tup9R322,
    ¬ @Equation1635 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1647 takes them (5 nodes). -/
def ordS9R322_Law1647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1647. -/
theorem noS9R322_Law1647 : ∀ v : Magma.tup9R322,
    ¬ @Equation1647 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1647) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1647) (by native_decide) v.1 v.2
    ((@Law1647.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (5 nodes). -/
def ordS9R322_Law1654 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1654. -/
theorem noS9R322_Law1654 : ∀ v : Magma.tup9R322,
    ¬ @Equation1654 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (4 nodes). -/
def ordS9R322_Law1658 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1658. -/
theorem noS9R322_Law1658 : ∀ v : Magma.tup9R322,
    ¬ @Equation1658 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (4 nodes). -/
def ordS9R322_Law1662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1662. -/
theorem noS9R322_Law1662 : ∀ v : Magma.tup9R322,
    ¬ @Equation1662 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (4 nodes). -/
def ordS9R322_Law1691 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1691. -/
theorem noS9R322_Law1691 : ∀ v : Magma.tup9R322,
    ¬ @Equation1691 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1731 takes them (4 nodes). -/
def ordS9R322_Law1731 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1731. -/
theorem noS9R322_Law1731 : ∀ v : Magma.tup9R322,
    ¬ @Equation1731 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1731) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1731) (by native_decide) v.1 v.2
    ((@Law1731.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (4 nodes). -/
def ordS9R322_Law1780 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1780. -/
theorem noS9R322_Law1780 : ∀ v : Magma.tup9R322,
    ¬ @Equation1780 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1838 takes them (4 nodes). -/
def ordS9R322_Law1838 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1838. -/
theorem noS9R322_Law1838 : ∀ v : Magma.tup9R322,
    ¬ @Equation1838 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1838) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1838) (by native_decide) v.1 v.2
    ((@Law1838.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (5 nodes). -/
def ordS9R322_Law1840 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1840. -/
theorem noS9R322_Law1840 : ∀ v : Magma.tup9R322,
    ¬ @Equation1840 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1850 takes them (5 nodes). -/
def ordS9R322_Law1850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1850. -/
theorem noS9R322_Law1850 : ∀ v : Magma.tup9R322,
    ¬ @Equation1850 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1850) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1850) (by native_decide) v.1 v.2
    ((@Law1850.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1861 takes them (4 nodes). -/
def ordS9R322_Law1861 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1861. -/
theorem noS9R322_Law1861 : ∀ v : Magma.tup9R322,
    ¬ @Equation1861 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1861) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1861) (by native_decide) v.1 v.2
    ((@Law1861.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (4 nodes). -/
def ordS9R322_Law1873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1873. -/
theorem noS9R322_Law1873 : ∀ v : Magma.tup9R322,
    ¬ @Equation1873 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (4 nodes). -/
def ordS9R322_Law1894 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1894. -/
theorem noS9R322_Law1894 : ∀ v : Magma.tup9R322,
    ¬ @Equation1894 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1921 takes them (4 nodes). -/
def ordS9R322_Law1921 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1921. -/
theorem noS9R322_Law1921 : ∀ v : Magma.tup9R322,
    ¬ @Equation1921 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1921) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1921) (by native_decide) v.1 v.2
    ((@Law1921.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (4 nodes). -/
def ordS9R322_Law1934 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1934. -/
theorem noS9R322_Law1934 : ∀ v : Magma.tup9R322,
    ¬ @Equation1934 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (4 nodes). -/
def ordS9R322_Law1949 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1949. -/
theorem noS9R322_Law1949 : ∀ v : Magma.tup9R322,
    ¬ @Equation1949 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2044 takes them (4 nodes). -/
def ordS9R322_Law2044 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2044. -/
theorem noS9R322_Law2044 : ∀ v : Magma.tup9R322,
    ¬ @Equation2044 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2044) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2044) (by native_decide) v.1 v.2
    ((@Law2044.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (5 nodes). -/
def ordS9R322_Law2053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2053. -/
theorem noS9R322_Law2053 : ∀ v : Magma.tup9R322,
    ¬ @Equation2053 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2060 takes them (5 nodes). -/
def ordS9R322_Law2060 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2060. -/
theorem noS9R322_Law2060 : ∀ v : Magma.tup9R322,
    ¬ @Equation2060 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2060) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2060) (by native_decide) v.1 v.2
    ((@Law2060.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2097 takes them (4 nodes). -/
def ordS9R322_Law2097 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2097. -/
theorem noS9R322_Law2097 : ∀ v : Magma.tup9R322,
    ¬ @Equation2097 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2097) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2097) (by native_decide) v.1 v.2
    ((@Law2097.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (4 nodes). -/
def ordS9R322_Law2137 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2137. -/
theorem noS9R322_Law2137 : ∀ v : Magma.tup9R322,
    ¬ @Equation2137 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2256 takes them (5 nodes). -/
def ordS9R322_Law2256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2256. -/
theorem noS9R322_Law2256 : ∀ v : Magma.tup9R322,
    ¬ @Equation2256 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2256) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2256) (by native_decide) v.1 v.2
    ((@Law2256.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2263 takes them (5 nodes). -/
def ordS9R322_Law2263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2263. -/
theorem noS9R322_Law2263 : ∀ v : Magma.tup9R322,
    ¬ @Equation2263 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2263) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2263) (by native_decide) v.1 v.2
    ((@Law2263.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (4 nodes). -/
def ordS9R322_Law2267 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2267. -/
theorem noS9R322_Law2267 : ∀ v : Magma.tup9R322,
    ¬ @Equation2267 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (4 nodes). -/
def ordS9R322_Law2303 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2303. -/
theorem noS9R322_Law2303 : ∀ v : Magma.tup9R322,
    ¬ @Equation2303 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2327 takes them (4 nodes). -/
def ordS9R322_Law2327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2327. -/
theorem noS9R322_Law2327 : ∀ v : Magma.tup9R322,
    ¬ @Equation2327 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2327) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2327) (by native_decide) v.1 v.2
    ((@Law2327.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2449 takes them (5 nodes). -/
def ordS9R322_Law2449 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2449. -/
theorem noS9R322_Law2449 : ∀ v : Magma.tup9R322,
    ¬ @Equation2449 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2449) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2449) (by native_decide) v.1 v.2
    ((@Law2449.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (4 nodes). -/
def ordS9R322_Law2457 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2457. -/
theorem noS9R322_Law2457 : ∀ v : Magma.tup9R322,
    ¬ @Equation2457 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2459 takes them (5 nodes). -/
def ordS9R322_Law2459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2459. -/
theorem noS9R322_Law2459 : ∀ v : Magma.tup9R322,
    ¬ @Equation2459 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2459) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2459) (by native_decide) v.1 v.2
    ((@Law2459.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (4 nodes). -/
def ordS9R322_Law2470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2470. -/
theorem noS9R322_Law2470 : ∀ v : Magma.tup9R322,
    ¬ @Equation2470 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- No member of the class satisfies any of these `90` equations. -/
theorem srch9R322_refutes_0 :
    FamilyRefutes Magma.srch9R322 [
      16, 26, 43, 53, 55, 72, 102, 105, 127, 160, 179, 212, 221, 228, 258, 263, 273, 315, 332,
      362, 387, 417, 419, 430, 436, 466, 500, 528, 575, 617, 620, 630, 642, 669, 703, 826, 836,
      843, 845, 909, 916, 1029, 1036, 1038, 1045, 1075, 1122, 1184, 1226, 1231, 1241, 1249, 1325,
      1432, 1434, 1444, 1455, 1525, 1632, 1635, 1647, 1654, 1658, 1662, 1691, 1731, 1780, 1838,
      1840, 1850, 1861, 1873, 1894, 1921, 1934, 1949, 2044, 2053, 2060, 2097, 2137, 2256, 2263,
      2267, 2303, 2327, 2449, 2457, 2459, 2470
    ] :=
  ⟨noS9R322_Law16, noS9R322_Law26, noS9R322_Law43, noS9R322_Law53, noS9R322_Law55, noS9R322_Law72, noS9R322_Law102, noS9R322_Law105, noS9R322_Law127, noS9R322_Law160, noS9R322_Law179, noS9R322_Law212, noS9R322_Law221, noS9R322_Law228, noS9R322_Law258, noS9R322_Law263, noS9R322_Law273, noS9R322_Law315, noS9R322_Law332, noS9R322_Law362, noS9R322_Law387, noS9R322_Law417, noS9R322_Law419, noS9R322_Law430, noS9R322_Law436, noS9R322_Law466, noS9R322_Law500, noS9R322_Law528, noS9R322_Law575, noS9R322_Law617, noS9R322_Law620, noS9R322_Law630, noS9R322_Law642, noS9R322_Law669, noS9R322_Law703, noS9R322_Law826, noS9R322_Law836, noS9R322_Law843, noS9R322_Law845, noS9R322_Law909, noS9R322_Law916, noS9R322_Law1029, noS9R322_Law1036, noS9R322_Law1038, noS9R322_Law1045, noS9R322_Law1075, noS9R322_Law1122, noS9R322_Law1184, noS9R322_Law1226, noS9R322_Law1231, noS9R322_Law1241, noS9R322_Law1249, noS9R322_Law1325, noS9R322_Law1432, noS9R322_Law1434, noS9R322_Law1444, noS9R322_Law1455, noS9R322_Law1525, noS9R322_Law1632, noS9R322_Law1635, noS9R322_Law1647, noS9R322_Law1654, noS9R322_Law1658, noS9R322_Law1662, noS9R322_Law1691, noS9R322_Law1731, noS9R322_Law1780, noS9R322_Law1838, noS9R322_Law1840, noS9R322_Law1850, noS9R322_Law1861, noS9R322_Law1873, noS9R322_Law1894, noS9R322_Law1921, noS9R322_Law1934, noS9R322_Law1949, noS9R322_Law2044, noS9R322_Law2053, noS9R322_Law2060, noS9R322_Law2097, noS9R322_Law2137, noS9R322_Law2256, noS9R322_Law2263, noS9R322_Law2267, noS9R322_Law2303, noS9R322_Law2327, noS9R322_Law2449, noS9R322_Law2457, noS9R322_Law2459, noS9R322_Law2470⟩
