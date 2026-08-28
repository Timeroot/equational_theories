import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 1 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 307 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 9 takes them (3 nodes). -/
def ordS11R173_Law9 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 9. -/
theorem noS11R173_Law9 : ∀ v : Magma.tup11R173,
    ¬ @Equation9 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law9) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law9) (by native_decide) v.1 v.2
    ((@Law9.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 10 takes them (4 nodes). -/
def ordS11R173_Law10 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 10. -/
theorem noS11R173_Law10 : ∀ v : Magma.tup11R173,
    ¬ @Equation10 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law10) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law10) (by native_decide) v.1 v.2
    ((@Law10.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 25 takes them (4 nodes). -/
def ordS11R173_Law25 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 25. -/
theorem noS11R173_Law25 : ∀ v : Magma.tup11R173,
    ¬ @Equation25 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law25) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law25) (by native_decide) v.1 v.2
    ((@Law25.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 28 takes them (3 nodes). -/
def ordS11R173_Law28 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 28. -/
theorem noS11R173_Law28 : ∀ v : Magma.tup11R173,
    ¬ @Equation28 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law28) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law28) (by native_decide) v.1 v.2
    ((@Law28.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 38 takes them (3 nodes). -/
def ordS11R173_Law38 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 38. -/
theorem noS11R173_Law38 : ∀ v : Magma.tup11R173,
    ¬ @Equation38 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law38) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law38) (by native_decide) v.1 v.2
    ((@Law38.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 39 takes them (3 nodes). -/
def ordS11R173_Law39 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 39. -/
theorem noS11R173_Law39 : ∀ v : Magma.tup11R173,
    ¬ @Equation39 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law39) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law39) (by native_decide) v.1 v.2
    ((@Law39.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 42 takes them (3 nodes). -/
def ordS11R173_Law42 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 42. -/
theorem noS11R173_Law42 : ∀ v : Magma.tup11R173,
    ¬ @Equation42 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law42) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law42) (by native_decide) v.1 v.2
    ((@Law42.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 45 takes them (3 nodes). -/
def ordS11R173_Law45 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 45. -/
theorem noS11R173_Law45 : ∀ v : Magma.tup11R173,
    ¬ @Equation45 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law45) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law45) (by native_decide) v.1 v.2
    ((@Law45.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 48 takes them (3 nodes). -/
def ordS11R173_Law48 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 48. -/
theorem noS11R173_Law48 : ∀ v : Magma.tup11R173,
    ¬ @Equation48 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law48) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law48) (by native_decide) v.1 v.2
    ((@Law48.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 49 takes them (4 nodes). -/
def ordS11R173_Law49 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 49. -/
theorem noS11R173_Law49 : ∀ v : Magma.tup11R173,
    ¬ @Equation49 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law49) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law49) (by native_decide) v.1 v.2
    ((@Law49.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 50 takes them (3 nodes). -/
def ordS11R173_Law50 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 50. -/
theorem noS11R173_Law50 : ∀ v : Magma.tup11R173,
    ¬ @Equation50 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law50) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law50) (by native_decide) v.1 v.2
    ((@Law50.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 51 takes them (3 nodes). -/
def ordS11R173_Law51 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 51. -/
theorem noS11R173_Law51 : ∀ v : Magma.tup11R173,
    ¬ @Equation51 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law51) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law51) (by native_decide) v.1 v.2
    ((@Law51.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 52 takes them (4 nodes). -/
def ordS11R173_Law52 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 52. -/
theorem noS11R173_Law52 : ∀ v : Magma.tup11R173,
    ¬ @Equation52 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law52) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law52) (by native_decide) v.1 v.2
    ((@Law52.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 58 takes them (4 nodes). -/
def ordS11R173_Law58 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 58. -/
theorem noS11R173_Law58 : ∀ v : Magma.tup11R173,
    ¬ @Equation58 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law58) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law58) (by native_decide) v.1 v.2
    ((@Law58.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 65 takes them (3 nodes). -/
def ordS11R173_Law65 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 65. -/
theorem noS11R173_Law65 : ∀ v : Magma.tup11R173,
    ¬ @Equation65 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law65) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law65) (by native_decide) v.1 v.2
    ((@Law65.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 75 takes them (3 nodes). -/
def ordS11R173_Law75 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 75. -/
theorem noS11R173_Law75 : ∀ v : Magma.tup11R173,
    ¬ @Equation75 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law75) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law75) (by native_decide) v.1 v.2
    ((@Law75.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 100 takes them (3 nodes). -/
def ordS11R173_Law100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 100. -/
theorem noS11R173_Law100 : ∀ v : Magma.tup11R173,
    ¬ @Equation100 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law100) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law100) (by native_decide) v.1 v.2
    ((@Law100.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 101 takes them (4 nodes). -/
def ordS11R173_Law101 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 101. -/
theorem noS11R173_Law101 : ∀ v : Magma.tup11R173,
    ¬ @Equation101 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law101) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law101) (by native_decide) v.1 v.2
    ((@Law101.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 103 takes them (3 nodes). -/
def ordS11R173_Law103 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 103. -/
theorem noS11R173_Law103 : ∀ v : Magma.tup11R173,
    ¬ @Equation103 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law103) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law103) (by native_decide) v.1 v.2
    ((@Law103.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 104 takes them (4 nodes). -/
def ordS11R173_Law104 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 104. -/
theorem noS11R173_Law104 : ∀ v : Magma.tup11R173,
    ¬ @Equation104 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law104) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law104) (by native_decide) v.1 v.2
    ((@Law104.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 105 takes them (3 nodes). -/
def ordS11R173_Law105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 105. -/
theorem noS11R173_Law105 : ∀ v : Magma.tup11R173,
    ¬ @Equation105 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law105) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law105) (by native_decide) v.1 v.2
    ((@Law105.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 107 takes them (4 nodes). -/
def ordS11R173_Law107 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 107. -/
theorem noS11R173_Law107 : ∀ v : Magma.tup11R173,
    ¬ @Equation107 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law107) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law107) (by native_decide) v.1 v.2
    ((@Law107.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 110 takes them (4 nodes). -/
def ordS11R173_Law110 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 110. -/
theorem noS11R173_Law110 : ∀ v : Magma.tup11R173,
    ¬ @Equation110 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law110) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law110) (by native_decide) v.1 v.2
    ((@Law110.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 117 takes them (3 nodes). -/
def ordS11R173_Law117 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 117. -/
theorem noS11R173_Law117 : ∀ v : Magma.tup11R173,
    ¬ @Equation117 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law117) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law117) (by native_decide) v.1 v.2
    ((@Law117.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 152 takes them (3 nodes). -/
def ordS11R173_Law152 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 152. -/
theorem noS11R173_Law152 : ∀ v : Magma.tup11R173,
    ¬ @Equation152 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law152) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law152) (by native_decide) v.1 v.2
    ((@Law152.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 153 takes them (4 nodes). -/
def ordS11R173_Law153 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 153. -/
theorem noS11R173_Law153 : ∀ v : Magma.tup11R173,
    ¬ @Equation153 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law153) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law153) (by native_decide) v.1 v.2
    ((@Law153.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 156 takes them (4 nodes). -/
def ordS11R173_Law156 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 156. -/
theorem noS11R173_Law156 : ∀ v : Magma.tup11R173,
    ¬ @Equation156 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law156) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law156) (by native_decide) v.1 v.2
    ((@Law156.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 166 takes them (3 nodes). -/
def ordS11R173_Law166 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 166. -/
theorem noS11R173_Law166 : ∀ v : Magma.tup11R173,
    ¬ @Equation166 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law166) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law166) (by native_decide) v.1 v.2
    ((@Law166.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 205 takes them (4 nodes). -/
def ordS11R173_Law205 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 205. -/
theorem noS11R173_Law205 : ∀ v : Magma.tup11R173,
    ¬ @Equation205 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law205) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law205) (by native_decide) v.1 v.2
    ((@Law205.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 208 takes them (4 nodes). -/
def ordS11R173_Law208 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 208. -/
theorem noS11R173_Law208 : ∀ v : Magma.tup11R173,
    ¬ @Equation208 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law208) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law208) (by native_decide) v.1 v.2
    ((@Law208.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 209 takes them (3 nodes). -/
def ordS11R173_Law209 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 209. -/
theorem noS11R173_Law209 : ∀ v : Magma.tup11R173,
    ¬ @Equation209 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law209) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law209) (by native_decide) v.1 v.2
    ((@Law209.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 211 takes them (4 nodes). -/
def ordS11R173_Law211 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 211. -/
theorem noS11R173_Law211 : ∀ v : Magma.tup11R173,
    ¬ @Equation211 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law211) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law211) (by native_decide) v.1 v.2
    ((@Law211.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 214 takes them (4 nodes). -/
def ordS11R173_Law214 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 214. -/
theorem noS11R173_Law214 : ∀ v : Magma.tup11R173,
    ¬ @Equation214 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law214) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law214) (by native_decide) v.1 v.2
    ((@Law214.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 218 takes them (3 nodes). -/
def ordS11R173_Law218 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 218. -/
theorem noS11R173_Law218 : ∀ v : Magma.tup11R173,
    ¬ @Equation218 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law218) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law218) (by native_decide) v.1 v.2
    ((@Law218.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 221 takes them (3 nodes). -/
def ordS11R173_Law221 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 221. -/
theorem noS11R173_Law221 : ∀ v : Magma.tup11R173,
    ¬ @Equation221 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law221) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law221) (by native_decide) v.1 v.2
    ((@Law221.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 238 takes them (3 nodes). -/
def ordS11R173_Law238 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 238. -/
theorem noS11R173_Law238 : ∀ v : Magma.tup11R173,
    ¬ @Equation238 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law238) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law238) (by native_decide) v.1 v.2
    ((@Law238.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 257 takes them (4 nodes). -/
def ordS11R173_Law257 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 257. -/
theorem noS11R173_Law257 : ∀ v : Magma.tup11R173,
    ¬ @Equation257 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law257) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law257) (by native_decide) v.1 v.2
    ((@Law257.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 260 takes them (4 nodes). -/
def ordS11R173_Law260 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 260. -/
theorem noS11R173_Law260 : ∀ v : Magma.tup11R173,
    ¬ @Equation260 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law260) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law260) (by native_decide) v.1 v.2
    ((@Law260.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 261 takes them (3 nodes). -/
def ordS11R173_Law261 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 261. -/
theorem noS11R173_Law261 : ∀ v : Magma.tup11R173,
    ¬ @Equation261 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law261) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law261) (by native_decide) v.1 v.2
    ((@Law261.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 264 takes them (3 nodes). -/
def ordS11R173_Law264 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 264. -/
theorem noS11R173_Law264 : ∀ v : Magma.tup11R173,
    ¬ @Equation264 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law264) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law264) (by native_decide) v.1 v.2
    ((@Law264.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 266 takes them (4 nodes). -/
def ordS11R173_Law266 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 266. -/
theorem noS11R173_Law266 : ∀ v : Magma.tup11R173,
    ¬ @Equation266 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law266) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law266) (by native_decide) v.1 v.2
    ((@Law266.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 270 takes them (3 nodes). -/
def ordS11R173_Law270 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 270. -/
theorem noS11R173_Law270 : ∀ v : Magma.tup11R173,
    ¬ @Equation270 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law270) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law270) (by native_decide) v.1 v.2
    ((@Law270.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 280 takes them (3 nodes). -/
def ordS11R173_Law280 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 280. -/
theorem noS11R173_Law280 : ∀ v : Magma.tup11R173,
    ¬ @Equation280 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law280) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law280) (by native_decide) v.1 v.2
    ((@Law280.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 290 takes them (3 nodes). -/
def ordS11R173_Law290 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 290. -/
theorem noS11R173_Law290 : ∀ v : Magma.tup11R173,
    ¬ @Equation290 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law290) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law290) (by native_decide) v.1 v.2
    ((@Law290.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 308 takes them (3 nodes). -/
def ordS11R173_Law308 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 308. -/
theorem noS11R173_Law308 : ∀ v : Magma.tup11R173,
    ¬ @Equation308 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law308) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law308) (by native_decide) v.1 v.2
    ((@Law308.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 309 takes them (4 nodes). -/
def ordS11R173_Law309 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 309. -/
theorem noS11R173_Law309 : ∀ v : Magma.tup11R173,
    ¬ @Equation309 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law309) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law309) (by native_decide) v.1 v.2
    ((@Law309.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 310 takes them (3 nodes). -/
def ordS11R173_Law310 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 310. -/
theorem noS11R173_Law310 : ∀ v : Magma.tup11R173,
    ¬ @Equation310 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law310) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law310) (by native_decide) v.1 v.2
    ((@Law310.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 311 takes them (3 nodes). -/
def ordS11R173_Law311 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 311. -/
theorem noS11R173_Law311 : ∀ v : Magma.tup11R173,
    ¬ @Equation311 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law311) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law311) (by native_decide) v.1 v.2
    ((@Law311.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 322 takes them (3 nodes). -/
def ordS11R173_Law322 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 322. -/
theorem noS11R173_Law322 : ∀ v : Magma.tup11R173,
    ¬ @Equation322 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law322) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law322) (by native_decide) v.1 v.2
    ((@Law322.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 323 takes them (4 nodes). -/
def ordS11R173_Law323 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 323. -/
theorem noS11R173_Law323 : ∀ v : Magma.tup11R173,
    ¬ @Equation323 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law323) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law323) (by native_decide) v.1 v.2
    ((@Law323.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 324 takes them (3 nodes). -/
def ordS11R173_Law324 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 324. -/
theorem noS11R173_Law324 : ∀ v : Magma.tup11R173,
    ¬ @Equation324 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law324) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law324) (by native_decide) v.1 v.2
    ((@Law324.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 325 takes them (3 nodes). -/
def ordS11R173_Law325 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 325. -/
theorem noS11R173_Law325 : ∀ v : Magma.tup11R173,
    ¬ @Equation325 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law325) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law325) (by native_decide) v.1 v.2
    ((@Law325.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 327 takes them (3 nodes). -/
def ordS11R173_Law327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 327. -/
theorem noS11R173_Law327 : ∀ v : Magma.tup11R173,
    ¬ @Equation327 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law327) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law327) (by native_decide) v.1 v.2
    ((@Law327.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 328 takes them (3 nodes). -/
def ordS11R173_Law328 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 328. -/
theorem noS11R173_Law328 : ∀ v : Magma.tup11R173,
    ¬ @Equation328 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law328) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law328) (by native_decide) v.1 v.2
    ((@Law328.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 329 takes them (4 nodes). -/
def ordS11R173_Law329 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 329. -/
theorem noS11R173_Law329 : ∀ v : Magma.tup11R173,
    ¬ @Equation329 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law329) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law329) (by native_decide) v.1 v.2
    ((@Law329.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 330 takes them (3 nodes). -/
def ordS11R173_Law330 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 330. -/
theorem noS11R173_Law330 : ∀ v : Magma.tup11R173,
    ¬ @Equation330 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law330) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law330) (by native_decide) v.1 v.2
    ((@Law330.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 331 takes them (3 nodes). -/
def ordS11R173_Law331 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 331. -/
theorem noS11R173_Law331 : ∀ v : Magma.tup11R173,
    ¬ @Equation331 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law331) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law331) (by native_decide) v.1 v.2
    ((@Law331.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 333 takes them (3 nodes). -/
def ordS11R173_Law333 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 333. -/
theorem noS11R173_Law333 : ∀ v : Magma.tup11R173,
    ¬ @Equation333 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law333) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law333) (by native_decide) v.1 v.2
    ((@Law333.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 361 takes them (4 nodes). -/
def ordS11R173_Law361 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 361. -/
theorem noS11R173_Law361 : ∀ v : Magma.tup11R173,
    ¬ @Equation361 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law361) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law361) (by native_decide) v.1 v.2
    ((@Law361.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 364 takes them (3 nodes). -/
def ordS11R173_Law364 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 364. -/
theorem noS11R173_Law364 : ∀ v : Magma.tup11R173,
    ¬ @Equation364 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law364) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law364) (by native_decide) v.1 v.2
    ((@Law364.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 367 takes them (3 nodes). -/
def ordS11R173_Law367 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 367. -/
theorem noS11R173_Law367 : ∀ v : Magma.tup11R173,
    ¬ @Equation367 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law367) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law367) (by native_decide) v.1 v.2
    ((@Law367.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 370 takes them (3 nodes). -/
def ordS11R173_Law370 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 370. -/
theorem noS11R173_Law370 : ∀ v : Magma.tup11R173,
    ¬ @Equation370 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law370) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law370) (by native_decide) v.1 v.2
    ((@Law370.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 377 takes them (3 nodes). -/
def ordS11R173_Law377 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 377. -/
theorem noS11R173_Law377 : ∀ v : Magma.tup11R173,
    ¬ @Equation377 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law377) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law377) (by native_decide) v.1 v.2
    ((@Law377.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 378 takes them (4 nodes). -/
def ordS11R173_Law378 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 378. -/
theorem noS11R173_Law378 : ∀ v : Magma.tup11R173,
    ¬ @Equation378 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law378) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law378) (by native_decide) v.1 v.2
    ((@Law378.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 381 takes them (4 nodes). -/
def ordS11R173_Law381 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 381. -/
theorem noS11R173_Law381 : ∀ v : Magma.tup11R173,
    ¬ @Equation381 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law381) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law381) (by native_decide) v.1 v.2
    ((@Law381.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 385 takes them (3 nodes). -/
def ordS11R173_Law385 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 385. -/
theorem noS11R173_Law385 : ∀ v : Magma.tup11R173,
    ¬ @Equation385 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law385) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law385) (by native_decide) v.1 v.2
    ((@Law385.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 388 takes them (3 nodes). -/
def ordS11R173_Law388 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 388. -/
theorem noS11R173_Law388 : ∀ v : Magma.tup11R173,
    ¬ @Equation388 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law388) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law388) (by native_decide) v.1 v.2
    ((@Law388.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 391 takes them (3 nodes). -/
def ordS11R173_Law391 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 391. -/
theorem noS11R173_Law391 : ∀ v : Magma.tup11R173,
    ¬ @Equation391 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law391) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law391) (by native_decide) v.1 v.2
    ((@Law391.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 395 takes them (3 nodes). -/
def ordS11R173_Law395 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 395. -/
theorem noS11R173_Law395 : ∀ v : Magma.tup11R173,
    ¬ @Equation395 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law395) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law395) (by native_decide) v.1 v.2
    ((@Law395.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 399 takes them (3 nodes). -/
def ordS11R173_Law399 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 399. -/
theorem noS11R173_Law399 : ∀ v : Magma.tup11R173,
    ¬ @Equation399 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law399) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law399) (by native_decide) v.1 v.2
    ((@Law399.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 403 takes them (3 nodes). -/
def ordS11R173_Law403 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 403. -/
theorem noS11R173_Law403 : ∀ v : Magma.tup11R173,
    ¬ @Equation403 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law403) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law403) (by native_decide) v.1 v.2
    ((@Law403.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 407 takes them (3 nodes). -/
def ordS11R173_Law407 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 407. -/
theorem noS11R173_Law407 : ∀ v : Magma.tup11R173,
    ¬ @Equation407 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law407) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law407) (by native_decide) v.1 v.2
    ((@Law407.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 412 takes them (3 nodes). -/
def ordS11R173_Law412 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 412. -/
theorem noS11R173_Law412 : ∀ v : Magma.tup11R173,
    ¬ @Equation412 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law412) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law412) (by native_decide) v.1 v.2
    ((@Law412.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 413 takes them (4 nodes). -/
def ordS11R173_Law413 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 413. -/
theorem noS11R173_Law413 : ∀ v : Magma.tup11R173,
    ¬ @Equation413 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law413) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law413) (by native_decide) v.1 v.2
    ((@Law413.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 414 takes them (3 nodes). -/
def ordS11R173_Law414 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 414. -/
theorem noS11R173_Law414 : ∀ v : Magma.tup11R173,
    ¬ @Equation414 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law414) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law414) (by native_decide) v.1 v.2
    ((@Law414.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 415 takes them (3 nodes). -/
def ordS11R173_Law415 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 415. -/
theorem noS11R173_Law415 : ∀ v : Magma.tup11R173,
    ¬ @Equation415 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law415) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law415) (by native_decide) v.1 v.2
    ((@Law415.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 416 takes them (4 nodes). -/
def ordS11R173_Law416 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 416. -/
theorem noS11R173_Law416 : ∀ v : Magma.tup11R173,
    ¬ @Equation416 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law416) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law416) (by native_decide) v.1 v.2
    ((@Law416.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 417 takes them (3 nodes). -/
def ordS11R173_Law417 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 417. -/
theorem noS11R173_Law417 : ∀ v : Magma.tup11R173,
    ¬ @Equation417 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 418 takes them (3 nodes). -/
def ordS11R173_Law418 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 418. -/
theorem noS11R173_Law418 : ∀ v : Magma.tup11R173,
    ¬ @Equation418 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law418) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law418) (by native_decide) v.1 v.2
    ((@Law418.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 420 takes them (3 nodes). -/
def ordS11R173_Law420 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 420. -/
theorem noS11R173_Law420 : ∀ v : Magma.tup11R173,
    ¬ @Equation420 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law420) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law420) (by native_decide) v.1 v.2
    ((@Law420.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 421 takes them (3 nodes). -/
def ordS11R173_Law421 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 421. -/
theorem noS11R173_Law421 : ∀ v : Magma.tup11R173,
    ¬ @Equation421 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law421) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law421) (by native_decide) v.1 v.2
    ((@Law421.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 422 takes them (4 nodes). -/
def ordS11R173_Law422 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 422. -/
theorem noS11R173_Law422 : ∀ v : Magma.tup11R173,
    ¬ @Equation422 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law422) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law422) (by native_decide) v.1 v.2
    ((@Law422.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 423 takes them (3 nodes). -/
def ordS11R173_Law423 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 423. -/
theorem noS11R173_Law423 : ∀ v : Magma.tup11R173,
    ¬ @Equation423 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law423) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law423) (by native_decide) v.1 v.2
    ((@Law423.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 424 takes them (3 nodes). -/
def ordS11R173_Law424 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 424. -/
theorem noS11R173_Law424 : ∀ v : Magma.tup11R173,
    ¬ @Equation424 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law424) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law424) (by native_decide) v.1 v.2
    ((@Law424.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 425 takes them (3 nodes). -/
def ordS11R173_Law425 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 425. -/
theorem noS11R173_Law425 : ∀ v : Magma.tup11R173,
    ¬ @Equation425 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law425) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law425) (by native_decide) v.1 v.2
    ((@Law425.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 426 takes them (4 nodes). -/
def ordS11R173_Law426 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 426. -/
theorem noS11R173_Law426 : ∀ v : Magma.tup11R173,
    ¬ @Equation426 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law426) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law426) (by native_decide) v.1 v.2
    ((@Law426.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 428 takes them (3 nodes). -/
def ordS11R173_Law428 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 428. -/
theorem noS11R173_Law428 : ∀ v : Magma.tup11R173,
    ¬ @Equation428 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law428) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law428) (by native_decide) v.1 v.2
    ((@Law428.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 429 takes them (4 nodes). -/
def ordS11R173_Law429 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 429. -/
theorem noS11R173_Law429 : ∀ v : Magma.tup11R173,
    ¬ @Equation429 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 430 takes them (3 nodes). -/
def ordS11R173_Law430 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 430. -/
theorem noS11R173_Law430 : ∀ v : Magma.tup11R173,
    ¬ @Equation430 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 432 takes them (4 nodes). -/
def ordS11R173_Law432 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 432. -/
theorem noS11R173_Law432 : ∀ v : Magma.tup11R173,
    ¬ @Equation432 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law432) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law432) (by native_decide) v.1 v.2
    ((@Law432.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 433 takes them (3 nodes). -/
def ordS11R173_Law433 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 433. -/
theorem noS11R173_Law433 : ∀ v : Magma.tup11R173,
    ¬ @Equation433 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law433) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law433) (by native_decide) v.1 v.2
    ((@Law433.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 439 takes them (4 nodes). -/
def ordS11R173_Law439 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 439. -/
theorem noS11R173_Law439 : ∀ v : Magma.tup11R173,
    ¬ @Equation439 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law439) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law439) (by native_decide) v.1 v.2
    ((@Law439.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch11R173_refutes_0 :
    FamilyRefutes Magma.srch11R173 [
      9, 10, 25, 28, 38, 39, 42, 45, 48, 49, 50, 51, 52, 58, 65, 75, 100, 101, 103, 104, 105,
      107, 110, 117, 152, 153, 156, 166, 205, 208, 209, 211, 214, 218, 221, 238, 257, 260, 261,
      264, 266, 270, 280, 290, 308, 309, 310, 311, 322, 323, 324, 325, 327, 328, 329, 330, 331,
      333, 361, 364, 367, 370, 377, 378, 381, 385, 388, 391, 395, 399, 403, 407, 412, 413, 414,
      415, 416, 417, 418, 420, 421, 422, 423, 424, 425, 426, 428, 429, 430, 432, 433, 439
    ] :=
  ⟨noS11R173_Law9, noS11R173_Law10, noS11R173_Law25, noS11R173_Law28, noS11R173_Law38, noS11R173_Law39, noS11R173_Law42, noS11R173_Law45, noS11R173_Law48, noS11R173_Law49, noS11R173_Law50, noS11R173_Law51, noS11R173_Law52, noS11R173_Law58, noS11R173_Law65, noS11R173_Law75, noS11R173_Law100, noS11R173_Law101, noS11R173_Law103, noS11R173_Law104, noS11R173_Law105, noS11R173_Law107, noS11R173_Law110, noS11R173_Law117, noS11R173_Law152, noS11R173_Law153, noS11R173_Law156, noS11R173_Law166, noS11R173_Law205, noS11R173_Law208, noS11R173_Law209, noS11R173_Law211, noS11R173_Law214, noS11R173_Law218, noS11R173_Law221, noS11R173_Law238, noS11R173_Law257, noS11R173_Law260, noS11R173_Law261, noS11R173_Law264, noS11R173_Law266, noS11R173_Law270, noS11R173_Law280, noS11R173_Law290, noS11R173_Law308, noS11R173_Law309, noS11R173_Law310, noS11R173_Law311, noS11R173_Law322, noS11R173_Law323, noS11R173_Law324, noS11R173_Law325, noS11R173_Law327, noS11R173_Law328, noS11R173_Law329, noS11R173_Law330, noS11R173_Law331, noS11R173_Law333, noS11R173_Law361, noS11R173_Law364, noS11R173_Law367, noS11R173_Law370, noS11R173_Law377, noS11R173_Law378, noS11R173_Law381, noS11R173_Law385, noS11R173_Law388, noS11R173_Law391, noS11R173_Law395, noS11R173_Law399, noS11R173_Law403, noS11R173_Law407, noS11R173_Law412, noS11R173_Law413, noS11R173_Law414, noS11R173_Law415, noS11R173_Law416, noS11R173_Law417, noS11R173_Law418, noS11R173_Law420, noS11R173_Law421, noS11R173_Law422, noS11R173_Law423, noS11R173_Law424, noS11R173_Law425, noS11R173_Law426, noS11R173_Law428, noS11R173_Law429, noS11R173_Law430, noS11R173_Law432, noS11R173_Law433, noS11R173_Law439⟩
