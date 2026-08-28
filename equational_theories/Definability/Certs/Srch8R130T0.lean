import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 1 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 297 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 9 takes them (3 nodes). -/
def ordS8R130_Law9 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 9. -/
theorem noS8R130_Law9 : ∀ v : Magma.tup8R130,
    ¬ @Equation9 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law9) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law9) (by native_decide) v.1 v.2
    ((@Law9.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 11 takes them (3 nodes). -/
def ordS8R130_Law11 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 11. -/
theorem noS8R130_Law11 : ∀ v : Magma.tup8R130,
    ¬ @Equation11 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law11) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law11) (by native_decide) v.1 v.2
    ((@Law11.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 16 takes them (3 nodes). -/
def ordS8R130_Law16 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 16. -/
theorem noS8R130_Law16 : ∀ v : Magma.tup8R130,
    ¬ @Equation16 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (3 nodes). -/
def ordS8R130_Law26 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 26. -/
theorem noS8R130_Law26 : ∀ v : Magma.tup8R130,
    ¬ @Equation26 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 28 takes them (3 nodes). -/
def ordS8R130_Law28 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 28. -/
theorem noS8R130_Law28 : ∀ v : Magma.tup8R130,
    ¬ @Equation28 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law28) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law28) (by native_decide) v.1 v.2
    ((@Law28.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 31 takes them (3 nodes). -/
def ordS8R130_Law31 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 31. -/
theorem noS8R130_Law31 : ∀ v : Magma.tup8R130,
    ¬ @Equation31 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law31) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law31) (by native_decide) v.1 v.2
    ((@Law31.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 48 takes them (3 nodes). -/
def ordS8R130_Law48 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 48. -/
theorem noS8R130_Law48 : ∀ v : Magma.tup8R130,
    ¬ @Equation48 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law48) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law48) (by native_decide) v.1 v.2
    ((@Law48.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 49 takes them (4 nodes). -/
def ordS8R130_Law49 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 49. -/
theorem noS8R130_Law49 : ∀ v : Magma.tup8R130,
    ¬ @Equation49 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law49) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law49) (by native_decide) v.1 v.2
    ((@Law49.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 50 takes them (3 nodes). -/
def ordS8R130_Law50 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 50. -/
theorem noS8R130_Law50 : ∀ v : Magma.tup8R130,
    ¬ @Equation50 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law50) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law50) (by native_decide) v.1 v.2
    ((@Law50.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 51 takes them (3 nodes). -/
def ordS8R130_Law51 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 51. -/
theorem noS8R130_Law51 : ∀ v : Magma.tup8R130,
    ¬ @Equation51 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law51) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law51) (by native_decide) v.1 v.2
    ((@Law51.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 55 takes them (4 nodes). -/
def ordS8R130_Law55 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 55. -/
theorem noS8R130_Law55 : ∀ v : Magma.tup8R130,
    ¬ @Equation55 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law55) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law55) (by native_decide) v.1 v.2
    ((@Law55.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 72 takes them (3 nodes). -/
def ordS8R130_Law72 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 72. -/
theorem noS8R130_Law72 : ∀ v : Magma.tup8R130,
    ¬ @Equation72 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law72) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law72) (by native_decide) v.1 v.2
    ((@Law72.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 75 takes them (3 nodes). -/
def ordS8R130_Law75 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 75. -/
theorem noS8R130_Law75 : ∀ v : Magma.tup8R130,
    ¬ @Equation75 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law75) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law75) (by native_decide) v.1 v.2
    ((@Law75.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 100 takes them (3 nodes). -/
def ordS8R130_Law100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 100. -/
theorem noS8R130_Law100 : ∀ v : Magma.tup8R130,
    ¬ @Equation100 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law100) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law100) (by native_decide) v.1 v.2
    ((@Law100.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 101 takes them (4 nodes). -/
def ordS8R130_Law101 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 101. -/
theorem noS8R130_Law101 : ∀ v : Magma.tup8R130,
    ¬ @Equation101 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law101) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law101) (by native_decide) v.1 v.2
    ((@Law101.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 102 takes them (3 nodes). -/
def ordS8R130_Law102 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 102. -/
theorem noS8R130_Law102 : ∀ v : Magma.tup8R130,
    ¬ @Equation102 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law102) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law102) (by native_decide) v.1 v.2
    ((@Law102.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 104 takes them (4 nodes). -/
def ordS8R130_Law104 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 104. -/
theorem noS8R130_Law104 : ∀ v : Magma.tup8R130,
    ¬ @Equation104 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law104) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law104) (by native_decide) v.1 v.2
    ((@Law104.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 105 takes them (3 nodes). -/
def ordS8R130_Law105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 105. -/
theorem noS8R130_Law105 : ∀ v : Magma.tup8R130,
    ¬ @Equation105 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law105) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law105) (by native_decide) v.1 v.2
    ((@Law105.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 107 takes them (4 nodes). -/
def ordS8R130_Law107 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 107. -/
theorem noS8R130_Law107 : ∀ v : Magma.tup8R130,
    ¬ @Equation107 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law107) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law107) (by native_decide) v.1 v.2
    ((@Law107.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 108 takes them (3 nodes). -/
def ordS8R130_Law108 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 108. -/
theorem noS8R130_Law108 : ∀ v : Magma.tup8R130,
    ¬ @Equation108 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law108) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law108) (by native_decide) v.1 v.2
    ((@Law108.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 109 takes them (3 nodes). -/
def ordS8R130_Law109 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 109. -/
theorem noS8R130_Law109 : ∀ v : Magma.tup8R130,
    ¬ @Equation109 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law109) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law109) (by native_decide) v.1 v.2
    ((@Law109.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 127 takes them (3 nodes). -/
def ordS8R130_Law127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 127. -/
theorem noS8R130_Law127 : ∀ v : Magma.tup8R130,
    ¬ @Equation127 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 152 takes them (3 nodes). -/
def ordS8R130_Law152 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 152. -/
theorem noS8R130_Law152 : ∀ v : Magma.tup8R130,
    ¬ @Equation152 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law152) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law152) (by native_decide) v.1 v.2
    ((@Law152.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (3 nodes). -/
def ordS8R130_Law160 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 160. -/
theorem noS8R130_Law160 : ∀ v : Magma.tup8R130,
    ¬ @Equation160 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 166 takes them (3 nodes). -/
def ordS8R130_Law166 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 166. -/
theorem noS8R130_Law166 : ∀ v : Magma.tup8R130,
    ¬ @Equation166 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law166) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law166) (by native_decide) v.1 v.2
    ((@Law166.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (3 nodes). -/
def ordS8R130_Law179 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 179. -/
theorem noS8R130_Law179 : ∀ v : Magma.tup8R130,
    ¬ @Equation179 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 205 takes them (4 nodes). -/
def ordS8R130_Law205 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 205. -/
theorem noS8R130_Law205 : ∀ v : Magma.tup8R130,
    ¬ @Equation205 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law205) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law205) (by native_decide) v.1 v.2
    ((@Law205.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 208 takes them (4 nodes). -/
def ordS8R130_Law208 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 208. -/
theorem noS8R130_Law208 : ∀ v : Magma.tup8R130,
    ¬ @Equation208 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law208) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law208) (by native_decide) v.1 v.2
    ((@Law208.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 211 takes them (4 nodes). -/
def ordS8R130_Law211 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 211. -/
theorem noS8R130_Law211 : ∀ v : Magma.tup8R130,
    ¬ @Equation211 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law211) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law211) (by native_decide) v.1 v.2
    ((@Law211.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (3 nodes). -/
def ordS8R130_Law212 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 212. -/
theorem noS8R130_Law212 : ∀ v : Magma.tup8R130,
    ¬ @Equation212 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 218 takes them (3 nodes). -/
def ordS8R130_Law218 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 218. -/
theorem noS8R130_Law218 : ∀ v : Magma.tup8R130,
    ¬ @Equation218 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law218) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law218) (by native_decide) v.1 v.2
    ((@Law218.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 221 takes them (3 nodes). -/
def ordS8R130_Law221 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 221. -/
theorem noS8R130_Law221 : ∀ v : Magma.tup8R130,
    ¬ @Equation221 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law221) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law221) (by native_decide) v.1 v.2
    ((@Law221.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 228 takes them (3 nodes). -/
def ordS8R130_Law228 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 228. -/
theorem noS8R130_Law228 : ∀ v : Magma.tup8R130,
    ¬ @Equation228 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law228) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law228) (by native_decide) v.1 v.2
    ((@Law228.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 231 takes them (3 nodes). -/
def ordS8R130_Law231 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 231. -/
theorem noS8R130_Law231 : ∀ v : Magma.tup8R130,
    ¬ @Equation231 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law231) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law231) (by native_decide) v.1 v.2
    ((@Law231.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 246 takes them (3 nodes). -/
def ordS8R130_Law246 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 246. -/
theorem noS8R130_Law246 : ∀ v : Magma.tup8R130,
    ¬ @Equation246 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law246) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law246) (by native_decide) v.1 v.2
    ((@Law246.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 258 takes them (3 nodes). -/
def ordS8R130_Law258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 258. -/
theorem noS8R130_Law258 : ∀ v : Magma.tup8R130,
    ¬ @Equation258 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law258) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law258) (by native_decide) v.1 v.2
    ((@Law258.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 260 takes them (4 nodes). -/
def ordS8R130_Law260 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 260. -/
theorem noS8R130_Law260 : ∀ v : Magma.tup8R130,
    ¬ @Equation260 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law260) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law260) (by native_decide) v.1 v.2
    ((@Law260.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 263 takes them (4 nodes). -/
def ordS8R130_Law263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 263. -/
theorem noS8R130_Law263 : ∀ v : Magma.tup8R130,
    ¬ @Equation263 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law263) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law263) (by native_decide) v.1 v.2
    ((@Law263.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 264 takes them (3 nodes). -/
def ordS8R130_Law264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 264. -/
theorem noS8R130_Law264 : ∀ v : Magma.tup8R130,
    ¬ @Equation264 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law264) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law264) (by native_decide) v.1 v.2
    ((@Law264.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 270 takes them (3 nodes). -/
def ordS8R130_Law270 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 270. -/
theorem noS8R130_Law270 : ∀ v : Magma.tup8R130,
    ¬ @Equation270 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law270) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law270) (by native_decide) v.1 v.2
    ((@Law270.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 280 takes them (3 nodes). -/
def ordS8R130_Law280 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 280. -/
theorem noS8R130_Law280 : ∀ v : Magma.tup8R130,
    ¬ @Equation280 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law280) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law280) (by native_decide) v.1 v.2
    ((@Law280.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 290 takes them (3 nodes). -/
def ordS8R130_Law290 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 290. -/
theorem noS8R130_Law290 : ∀ v : Magma.tup8R130,
    ¬ @Equation290 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law290) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law290) (by native_decide) v.1 v.2
    ((@Law290.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 308 takes them (3 nodes). -/
def ordS8R130_Law308 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 308. -/
theorem noS8R130_Law308 : ∀ v : Magma.tup8R130,
    ¬ @Equation308 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law308) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law308) (by native_decide) v.1 v.2
    ((@Law308.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 310 takes them (3 nodes). -/
def ordS8R130_Law310 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 310. -/
theorem noS8R130_Law310 : ∀ v : Magma.tup8R130,
    ¬ @Equation310 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law310) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law310) (by native_decide) v.1 v.2
    ((@Law310.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 312 takes them (3 nodes). -/
def ordS8R130_Law312 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 312. -/
theorem noS8R130_Law312 : ∀ v : Magma.tup8R130,
    ¬ @Equation312 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law312) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law312) (by native_decide) v.1 v.2
    ((@Law312.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 315 takes them (3 nodes). -/
def ordS8R130_Law315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 315. -/
theorem noS8R130_Law315 : ∀ v : Magma.tup8R130,
    ¬ @Equation315 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law315) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law315) (by native_decide) v.1 v.2
    ((@Law315.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 323 takes them (4 nodes). -/
def ordS8R130_Law323 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 323. -/
theorem noS8R130_Law323 : ∀ v : Magma.tup8R130,
    ¬ @Equation323 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law323) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law323) (by native_decide) v.1 v.2
    ((@Law323.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 325 takes them (3 nodes). -/
def ordS8R130_Law325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 325. -/
theorem noS8R130_Law325 : ∀ v : Magma.tup8R130,
    ¬ @Equation325 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law325) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law325) (by native_decide) v.1 v.2
    ((@Law325.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 333 takes them (3 nodes). -/
def ordS8R130_Law333 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 333. -/
theorem noS8R130_Law333 : ∀ v : Magma.tup8R130,
    ¬ @Equation333 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law333) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law333) (by native_decide) v.1 v.2
    ((@Law333.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 360 takes them (3 nodes). -/
def ordS8R130_Law360 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 360. -/
theorem noS8R130_Law360 : ∀ v : Magma.tup8R130,
    ¬ @Equation360 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law360) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law360) (by native_decide) v.1 v.2
    ((@Law360.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 362 takes them (3 nodes). -/
def ordS8R130_Law362 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 362. -/
theorem noS8R130_Law362 : ∀ v : Magma.tup8R130,
    ¬ @Equation362 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law362) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law362) (by native_decide) v.1 v.2
    ((@Law362.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 364 takes them (3 nodes). -/
def ordS8R130_Law364 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 364. -/
theorem noS8R130_Law364 : ∀ v : Magma.tup8R130,
    ¬ @Equation364 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law364) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law364) (by native_decide) v.1 v.2
    ((@Law364.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 367 takes them (3 nodes). -/
def ordS8R130_Law367 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 367. -/
theorem noS8R130_Law367 : ∀ v : Magma.tup8R130,
    ¬ @Equation367 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law367) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law367) (by native_decide) v.1 v.2
    ((@Law367.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 377 takes them (3 nodes). -/
def ordS8R130_Law377 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 377. -/
theorem noS8R130_Law377 : ∀ v : Magma.tup8R130,
    ¬ @Equation377 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law377) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law377) (by native_decide) v.1 v.2
    ((@Law377.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 378 takes them (4 nodes). -/
def ordS8R130_Law378 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 378. -/
theorem noS8R130_Law378 : ∀ v : Magma.tup8R130,
    ¬ @Equation378 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law378) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law378) (by native_decide) v.1 v.2
    ((@Law378.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 385 takes them (3 nodes). -/
def ordS8R130_Law385 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 385. -/
theorem noS8R130_Law385 : ∀ v : Magma.tup8R130,
    ¬ @Equation385 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law385) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law385) (by native_decide) v.1 v.2
    ((@Law385.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 412 takes them (3 nodes). -/
def ordS8R130_Law412 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 412. -/
theorem noS8R130_Law412 : ∀ v : Magma.tup8R130,
    ¬ @Equation412 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law412) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law412) (by native_decide) v.1 v.2
    ((@Law412.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 413 takes them (4 nodes). -/
def ordS8R130_Law413 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 413. -/
theorem noS8R130_Law413 : ∀ v : Magma.tup8R130,
    ¬ @Equation413 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law413) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law413) (by native_decide) v.1 v.2
    ((@Law413.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 414 takes them (3 nodes). -/
def ordS8R130_Law414 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 414. -/
theorem noS8R130_Law414 : ∀ v : Magma.tup8R130,
    ¬ @Equation414 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law414) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law414) (by native_decide) v.1 v.2
    ((@Law414.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 415 takes them (3 nodes). -/
def ordS8R130_Law415 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 415. -/
theorem noS8R130_Law415 : ∀ v : Magma.tup8R130,
    ¬ @Equation415 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law415) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law415) (by native_decide) v.1 v.2
    ((@Law415.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 416 takes them (4 nodes). -/
def ordS8R130_Law416 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 416. -/
theorem noS8R130_Law416 : ∀ v : Magma.tup8R130,
    ¬ @Equation416 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law416) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law416) (by native_decide) v.1 v.2
    ((@Law416.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 417 takes them (3 nodes). -/
def ordS8R130_Law417 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 417. -/
theorem noS8R130_Law417 : ∀ v : Magma.tup8R130,
    ¬ @Equation417 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 418 takes them (3 nodes). -/
def ordS8R130_Law418 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 418. -/
theorem noS8R130_Law418 : ∀ v : Magma.tup8R130,
    ¬ @Equation418 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law418) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law418) (by native_decide) v.1 v.2
    ((@Law418.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 419 takes them (4 nodes). -/
def ordS8R130_Law419 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 419. -/
theorem noS8R130_Law419 : ∀ v : Magma.tup8R130,
    ¬ @Equation419 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 420 takes them (3 nodes). -/
def ordS8R130_Law420 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 420. -/
theorem noS8R130_Law420 : ∀ v : Magma.tup8R130,
    ¬ @Equation420 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law420) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law420) (by native_decide) v.1 v.2
    ((@Law420.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 421 takes them (3 nodes). -/
def ordS8R130_Law421 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 421. -/
theorem noS8R130_Law421 : ∀ v : Magma.tup8R130,
    ¬ @Equation421 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law421) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law421) (by native_decide) v.1 v.2
    ((@Law421.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 422 takes them (4 nodes). -/
def ordS8R130_Law422 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 422. -/
theorem noS8R130_Law422 : ∀ v : Magma.tup8R130,
    ¬ @Equation422 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law422) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law422) (by native_decide) v.1 v.2
    ((@Law422.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 423 takes them (3 nodes). -/
def ordS8R130_Law423 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 423. -/
theorem noS8R130_Law423 : ∀ v : Magma.tup8R130,
    ¬ @Equation423 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law423) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law423) (by native_decide) v.1 v.2
    ((@Law423.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 424 takes them (3 nodes). -/
def ordS8R130_Law424 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 424. -/
theorem noS8R130_Law424 : ∀ v : Magma.tup8R130,
    ¬ @Equation424 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law424) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law424) (by native_decide) v.1 v.2
    ((@Law424.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 425 takes them (3 nodes). -/
def ordS8R130_Law425 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 425. -/
theorem noS8R130_Law425 : ∀ v : Magma.tup8R130,
    ¬ @Equation425 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law425) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law425) (by native_decide) v.1 v.2
    ((@Law425.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 429 takes them (4 nodes). -/
def ordS8R130_Law429 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 429. -/
theorem noS8R130_Law429 : ∀ v : Magma.tup8R130,
    ¬ @Equation429 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 430 takes them (3 nodes). -/
def ordS8R130_Law430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 430. -/
theorem noS8R130_Law430 : ∀ v : Magma.tup8R130,
    ¬ @Equation430 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 436 takes them (4 nodes). -/
def ordS8R130_Law436 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 436. -/
theorem noS8R130_Law436 : ∀ v : Magma.tup8R130,
    ¬ @Equation436 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law436) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law436) (by native_decide) v.1 v.2
    ((@Law436.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 439 takes them (4 nodes). -/
def ordS8R130_Law439 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 439. -/
theorem noS8R130_Law439 : ∀ v : Magma.tup8R130,
    ¬ @Equation439 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law439) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law439) (by native_decide) v.1 v.2
    ((@Law439.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 440 takes them (3 nodes). -/
def ordS8R130_Law440 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 440. -/
theorem noS8R130_Law440 : ∀ v : Magma.tup8R130,
    ¬ @Equation440 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law440) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law440) (by native_decide) v.1 v.2
    ((@Law440.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 444 takes them (3 nodes). -/
def ordS8R130_Law444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 444. -/
theorem noS8R130_Law444 : ∀ v : Magma.tup8R130,
    ¬ @Equation444 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law444) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law444) (by native_decide) v.1 v.2
    ((@Law444.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 452 takes them (3 nodes). -/
def ordS8R130_Law452 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 452. -/
theorem noS8R130_Law452 : ∀ v : Magma.tup8R130,
    ¬ @Equation452 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law452) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law452) (by native_decide) v.1 v.2
    ((@Law452.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 455 takes them (3 nodes). -/
def ordS8R130_Law455 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 455. -/
theorem noS8R130_Law455 : ∀ v : Magma.tup8R130,
    ¬ @Equation455 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law455) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law455) (by native_decide) v.1 v.2
    ((@Law455.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (3 nodes). -/
def ordS8R130_Law466 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 466. -/
theorem noS8R130_Law466 : ∀ v : Magma.tup8R130,
    ¬ @Equation466 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 473 takes them (3 nodes). -/
def ordS8R130_Law473 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 473. -/
theorem noS8R130_Law473 : ∀ v : Magma.tup8R130,
    ¬ @Equation473 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (3 nodes). -/
def ordS8R130_Law500 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 500. -/
theorem noS8R130_Law500 : ∀ v : Magma.tup8R130,
    ¬ @Equation500 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 510 takes them (3 nodes). -/
def ordS8R130_Law510 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 510. -/
theorem noS8R130_Law510 : ∀ v : Magma.tup8R130,
    ¬ @Equation510 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law510) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law510) (by native_decide) v.1 v.2
    ((@Law510.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 513 takes them (3 nodes). -/
def ordS8R130_Law513 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 513. -/
theorem noS8R130_Law513 : ∀ v : Magma.tup8R130,
    ¬ @Equation513 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law513) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law513) (by native_decide) v.1 v.2
    ((@Law513.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (3 nodes). -/
def ordS8R130_Law528 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 528. -/
theorem noS8R130_Law528 : ∀ v : Magma.tup8R130,
    ¬ @Equation528 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 562 takes them (3 nodes). -/
def ordS8R130_Law562 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 562. -/
theorem noS8R130_Law562 : ∀ v : Magma.tup8R130,
    ¬ @Equation562 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (3 nodes). -/
def ordS8R130_Law575 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 575. -/
theorem noS8R130_Law575 : ∀ v : Magma.tup8R130,
    ¬ @Equation575 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 615 takes them (3 nodes). -/
def ordS8R130_Law615 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 615. -/
theorem noS8R130_Law615 : ∀ v : Magma.tup8R130,
    ¬ @Equation615 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law615) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law615) (by native_decide) v.1 v.2
    ((@Law615.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 616 takes them (4 nodes). -/
def ordS8R130_Law616 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 616. -/
theorem noS8R130_Law616 : ∀ v : Magma.tup8R130,
    ¬ @Equation616 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law616) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law616) (by native_decide) v.1 v.2
    ((@Law616.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 617 takes them (3 nodes). -/
def ordS8R130_Law617 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 617. -/
theorem noS8R130_Law617 : ∀ v : Magma.tup8R130,
    ¬ @Equation617 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law617) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law617) (by native_decide) v.1 v.2
    ((@Law617.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 618 takes them (3 nodes). -/
def ordS8R130_Law618 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 618. -/
theorem noS8R130_Law618 : ∀ v : Magma.tup8R130,
    ¬ @Equation618 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law618) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law618) (by native_decide) v.1 v.2
    ((@Law618.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 619 takes them (4 nodes). -/
def ordS8R130_Law619 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 619. -/
theorem noS8R130_Law619 : ∀ v : Magma.tup8R130,
    ¬ @Equation619 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law619) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law619) (by native_decide) v.1 v.2
    ((@Law619.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (3 nodes). -/
def ordS8R130_Law620 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 620. -/
theorem noS8R130_Law620 : ∀ v : Magma.tup8R130,
    ¬ @Equation620 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch8R130_refutes_0 :
    FamilyRefutes Magma.srch8R130 [
      9, 11, 16, 26, 28, 31, 48, 49, 50, 51, 55, 72, 75, 100, 101, 102, 104, 105, 107, 108, 109,
      127, 152, 160, 166, 179, 205, 208, 211, 212, 218, 221, 228, 231, 246, 258, 260, 263, 264,
      270, 280, 290, 308, 310, 312, 315, 323, 325, 333, 360, 362, 364, 367, 377, 378, 385, 412,
      413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 429, 430, 436, 439, 440,
      444, 452, 455, 466, 473, 500, 510, 513, 528, 562, 575, 615, 616, 617, 618, 619, 620
    ] :=
  ⟨noS8R130_Law9, noS8R130_Law11, noS8R130_Law16, noS8R130_Law26, noS8R130_Law28, noS8R130_Law31, noS8R130_Law48, noS8R130_Law49, noS8R130_Law50, noS8R130_Law51, noS8R130_Law55, noS8R130_Law72, noS8R130_Law75, noS8R130_Law100, noS8R130_Law101, noS8R130_Law102, noS8R130_Law104, noS8R130_Law105, noS8R130_Law107, noS8R130_Law108, noS8R130_Law109, noS8R130_Law127, noS8R130_Law152, noS8R130_Law160, noS8R130_Law166, noS8R130_Law179, noS8R130_Law205, noS8R130_Law208, noS8R130_Law211, noS8R130_Law212, noS8R130_Law218, noS8R130_Law221, noS8R130_Law228, noS8R130_Law231, noS8R130_Law246, noS8R130_Law258, noS8R130_Law260, noS8R130_Law263, noS8R130_Law264, noS8R130_Law270, noS8R130_Law280, noS8R130_Law290, noS8R130_Law308, noS8R130_Law310, noS8R130_Law312, noS8R130_Law315, noS8R130_Law323, noS8R130_Law325, noS8R130_Law333, noS8R130_Law360, noS8R130_Law362, noS8R130_Law364, noS8R130_Law367, noS8R130_Law377, noS8R130_Law378, noS8R130_Law385, noS8R130_Law412, noS8R130_Law413, noS8R130_Law414, noS8R130_Law415, noS8R130_Law416, noS8R130_Law417, noS8R130_Law418, noS8R130_Law419, noS8R130_Law420, noS8R130_Law421, noS8R130_Law422, noS8R130_Law423, noS8R130_Law424, noS8R130_Law425, noS8R130_Law429, noS8R130_Law430, noS8R130_Law436, noS8R130_Law439, noS8R130_Law440, noS8R130_Law444, noS8R130_Law452, noS8R130_Law455, noS8R130_Law466, noS8R130_Law473, noS8R130_Law500, noS8R130_Law510, noS8R130_Law513, noS8R130_Law528, noS8R130_Law562, noS8R130_Law575, noS8R130_Law615, noS8R130_Law616, noS8R130_Law617, noS8R130_Law618, noS8R130_Law619, noS8R130_Law620⟩
