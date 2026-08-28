import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 1 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `79` equations here, 814 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 10 takes them (16 nodes). -/
def ordS8R164_Law10 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 10. -/
theorem noS8R164_Law10 : ∀ v : Magma.tup8R164,
    ¬ @Equation10 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law10) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law10) (by native_decide) v.1 v.2
    ((@Law10.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 25 takes them (16 nodes). -/
def ordS8R164_Law25 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 25. -/
theorem noS8R164_Law25 : ∀ v : Magma.tup8R164,
    ¬ @Equation25 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law25) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law25) (by native_decide) v.1 v.2
    ((@Law25.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 38 takes them (9 nodes). -/
def ordS8R164_Law38 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 38. -/
theorem noS8R164_Law38 : ∀ v : Magma.tup8R164,
    ¬ @Equation38 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law38) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law38) (by native_decide) v.1 v.2
    ((@Law38.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 39 takes them (10 nodes). -/
def ordS8R164_Law39 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 39. -/
theorem noS8R164_Law39 : ∀ v : Magma.tup8R164,
    ¬ @Equation39 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law39) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law39) (by native_decide) v.1 v.2
    ((@Law39.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 41 takes them (6 nodes). -/
def ordS8R164_Law41 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 41. -/
theorem noS8R164_Law41 : ∀ v : Magma.tup8R164,
    ¬ @Equation41 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law41) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law41) (by native_decide) v.1 v.2
    ((@Law41.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 42 takes them (9 nodes). -/
def ordS8R164_Law42 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 42. -/
theorem noS8R164_Law42 : ∀ v : Magma.tup8R164,
    ¬ @Equation42 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law42) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law42) (by native_decide) v.1 v.2
    ((@Law42.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 44 takes them (6 nodes). -/
def ordS8R164_Law44 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 44. -/
theorem noS8R164_Law44 : ∀ v : Magma.tup8R164,
    ¬ @Equation44 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law44) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law44) (by native_decide) v.1 v.2
    ((@Law44.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 45 takes them (10 nodes). -/
def ordS8R164_Law45 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 45. -/
theorem noS8R164_Law45 : ∀ v : Magma.tup8R164,
    ¬ @Equation45 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law45) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law45) (by native_decide) v.1 v.2
    ((@Law45.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 46 takes them (6 nodes). -/
def ordS8R164_Law46 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 46. -/
theorem noS8R164_Law46 : ∀ v : Magma.tup8R164,
    ¬ @Equation46 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law46) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law46) (by native_decide) v.1 v.2
    ((@Law46.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 101 takes them (17 nodes). -/
def ordS8R164_Law101 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 101. -/
theorem noS8R164_Law101 : ∀ v : Magma.tup8R164,
    ¬ @Equation101 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law101) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law101) (by native_decide) v.1 v.2
    ((@Law101.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 104 takes them (18 nodes). -/
def ordS8R164_Law104 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 104. -/
theorem noS8R164_Law104 : ∀ v : Magma.tup8R164,
    ¬ @Equation104 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law104) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law104) (by native_decide) v.1 v.2
    ((@Law104.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 106 takes them (10 nodes). -/
def ordS8R164_Law106 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 106. -/
theorem noS8R164_Law106 : ∀ v : Magma.tup8R164,
    ¬ @Equation106 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law106) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law106) (by native_decide) v.1 v.2
    ((@Law106.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 110 takes them (16 nodes). -/
def ordS8R164_Law110 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 110. -/
theorem noS8R164_Law110 : ∀ v : Magma.tup8R164,
    ¬ @Equation110 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law110) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law110) (by native_decide) v.1 v.2
    ((@Law110.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 111 takes them (10 nodes). -/
def ordS8R164_Law111 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 111. -/
theorem noS8R164_Law111 : ∀ v : Magma.tup8R164,
    ¬ @Equation111 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law111) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law111) (by native_decide) v.1 v.2
    ((@Law111.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 152 takes them (8 nodes). -/
def ordS8R164_Law152 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 152. -/
theorem noS8R164_Law152 : ∀ v : Magma.tup8R164,
    ¬ @Equation152 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law152) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law152) (by native_decide) v.1 v.2
    ((@Law152.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 153 takes them (14 nodes). -/
def ordS8R164_Law153 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 153. -/
theorem noS8R164_Law153 : ∀ v : Magma.tup8R164,
    ¬ @Equation153 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law153) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law153) (by native_decide) v.1 v.2
    ((@Law153.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 156 takes them (14 nodes). -/
def ordS8R164_Law156 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 156. -/
theorem noS8R164_Law156 : ∀ v : Magma.tup8R164,
    ¬ @Equation156 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law156) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law156) (by native_decide) v.1 v.2
    ((@Law156.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 166 takes them (9 nodes). -/
def ordS8R164_Law166 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 166. -/
theorem noS8R164_Law166 : ∀ v : Magma.tup8R164,
    ¬ @Equation166 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law166) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law166) (by native_decide) v.1 v.2
    ((@Law166.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 205 takes them (18 nodes). -/
def ordS8R164_Law205 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 205. -/
theorem noS8R164_Law205 : ∀ v : Magma.tup8R164,
    ¬ @Equation205 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law205) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law205) (by native_decide) v.1 v.2
    ((@Law205.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 208 takes them (17 nodes). -/
def ordS8R164_Law208 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 208. -/
theorem noS8R164_Law208 : ∀ v : Magma.tup8R164,
    ¬ @Equation208 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law208) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law208) (by native_decide) v.1 v.2
    ((@Law208.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 214 takes them (16 nodes). -/
def ordS8R164_Law214 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 214. -/
theorem noS8R164_Law214 : ∀ v : Magma.tup8R164,
    ¬ @Equation214 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law214) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law214) (by native_decide) v.1 v.2
    ((@Law214.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 224 takes them (11 nodes). -/
def ordS8R164_Law224 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 224. -/
theorem noS8R164_Law224 : ∀ v : Magma.tup8R164,
    ¬ @Equation224 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law224) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law224) (by native_decide) v.1 v.2
    ((@Law224.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 242 takes them (9 nodes). -/
def ordS8R164_Law242 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 242. -/
theorem noS8R164_Law242 : ∀ v : Magma.tup8R164,
    ¬ @Equation242 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law242) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law242) (by native_decide) v.1 v.2
    ((@Law242.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 308 takes them (11 nodes). -/
def ordS8R164_Law308 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 308. -/
theorem noS8R164_Law308 : ∀ v : Magma.tup8R164,
    ¬ @Equation308 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law308) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law308) (by native_decide) v.1 v.2
    ((@Law308.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 309 takes them (20 nodes). -/
def ordS8R164_Law309 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 309. -/
theorem noS8R164_Law309 : ∀ v : Magma.tup8R164,
    ¬ @Equation309 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law309) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law309) (by native_decide) v.1 v.2
    ((@Law309.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 311 takes them (9 nodes). -/
def ordS8R164_Law311 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 311. -/
theorem noS8R164_Law311 : ∀ v : Magma.tup8R164,
    ¬ @Equation311 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law311) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law311) (by native_decide) v.1 v.2
    ((@Law311.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 313 takes them (13 nodes). -/
def ordS8R164_Law313 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 313. -/
theorem noS8R164_Law313 : ∀ v : Magma.tup8R164,
    ¬ @Equation313 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law313) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law313) (by native_decide) v.1 v.2
    ((@Law313.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 314 takes them (6 nodes). -/
def ordS8R164_Law314 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 314. -/
theorem noS8R164_Law314 : ∀ v : Magma.tup8R164,
    ¬ @Equation314 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law314) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law314) (by native_decide) v.1 v.2
    ((@Law314.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 317 takes them (8 nodes). -/
def ordS8R164_Law317 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 317. -/
theorem noS8R164_Law317 : ∀ v : Magma.tup8R164,
    ¬ @Equation317 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law317) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law317) (by native_decide) v.1 v.2
    ((@Law317.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 318 takes them (10 nodes). -/
def ordS8R164_Law318 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 318. -/
theorem noS8R164_Law318 : ∀ v : Magma.tup8R164,
    ¬ @Equation318 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law318) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law318) (by native_decide) v.1 v.2
    ((@Law318.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 319 takes them (12 nodes). -/
def ordS8R164_Law319 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 319. -/
theorem noS8R164_Law319 : ∀ v : Magma.tup8R164,
    ¬ @Equation319 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law319) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law319) (by native_decide) v.1 v.2
    ((@Law319.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 321 takes them (6 nodes). -/
def ordS8R164_Law321 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 321. -/
theorem noS8R164_Law321 : ∀ v : Magma.tup8R164,
    ¬ @Equation321 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law321) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law321) (by native_decide) v.1 v.2
    ((@Law321.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 322 takes them (9 nodes). -/
def ordS8R164_Law322 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 322. -/
theorem noS8R164_Law322 : ∀ v : Magma.tup8R164,
    ¬ @Equation322 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law322) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law322) (by native_decide) v.1 v.2
    ((@Law322.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 323 takes them (28 nodes). -/
def ordS8R164_Law323 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 323. -/
theorem noS8R164_Law323 : ∀ v : Magma.tup8R164,
    ¬ @Equation323 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law323) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law323) (by native_decide) v.1 v.2
    ((@Law323.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 324 takes them (9 nodes). -/
def ordS8R164_Law324 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 324. -/
theorem noS8R164_Law324 : ∀ v : Magma.tup8R164,
    ¬ @Equation324 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law324) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law324) (by native_decide) v.1 v.2
    ((@Law324.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 325 takes them (17 nodes). -/
def ordS8R164_Law325 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 325. -/
theorem noS8R164_Law325 : ∀ v : Magma.tup8R164,
    ¬ @Equation325 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law325) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law325) (by native_decide) v.1 v.2
    ((@Law325.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 327 takes them (9 nodes). -/
def ordS8R164_Law327 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 327. -/
theorem noS8R164_Law327 : ∀ v : Magma.tup8R164,
    ¬ @Equation327 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law327) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law327) (by native_decide) v.1 v.2
    ((@Law327.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 328 takes them (9 nodes). -/
def ordS8R164_Law328 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 328. -/
theorem noS8R164_Law328 : ∀ v : Magma.tup8R164,
    ¬ @Equation328 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law328) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law328) (by native_decide) v.1 v.2
    ((@Law328.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 329 takes them (13 nodes). -/
def ordS8R164_Law329 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 329. -/
theorem noS8R164_Law329 : ∀ v : Magma.tup8R164,
    ¬ @Equation329 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law329) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law329) (by native_decide) v.1 v.2
    ((@Law329.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 330 takes them (9 nodes). -/
def ordS8R164_Law330 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 330. -/
theorem noS8R164_Law330 : ∀ v : Magma.tup8R164,
    ¬ @Equation330 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law330) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law330) (by native_decide) v.1 v.2
    ((@Law330.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 331 takes them (9 nodes). -/
def ordS8R164_Law331 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 331. -/
theorem noS8R164_Law331 : ∀ v : Magma.tup8R164,
    ¬ @Equation331 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law331) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law331) (by native_decide) v.1 v.2
    ((@Law331.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 333 takes them (17 nodes). -/
def ordS8R164_Law333 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 333. -/
theorem noS8R164_Law333 : ∀ v : Magma.tup8R164,
    ¬ @Equation333 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law333) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law333) (by native_decide) v.1 v.2
    ((@Law333.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 334 takes them (6 nodes). -/
def ordS8R164_Law334 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 334. -/
theorem noS8R164_Law334 : ∀ v : Magma.tup8R164,
    ¬ @Equation334 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law334) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law334) (by native_decide) v.1 v.2
    ((@Law334.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 335 takes them (11 nodes). -/
def ordS8R164_Law335 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 335. -/
theorem noS8R164_Law335 : ∀ v : Magma.tup8R164,
    ¬ @Equation335 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law335) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law335) (by native_decide) v.1 v.2
    ((@Law335.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 336 takes them (10 nodes). -/
def ordS8R164_Law336 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 336. -/
theorem noS8R164_Law336 : ∀ v : Magma.tup8R164,
    ¬ @Equation336 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law336) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law336) (by native_decide) v.1 v.2
    ((@Law336.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 337 takes them (6 nodes). -/
def ordS8R164_Law337 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 337. -/
theorem noS8R164_Law337 : ∀ v : Magma.tup8R164,
    ¬ @Equation337 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law337) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law337) (by native_decide) v.1 v.2
    ((@Law337.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 338 takes them (7 nodes). -/
def ordS8R164_Law338 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 338. -/
theorem noS8R164_Law338 : ∀ v : Magma.tup8R164,
    ¬ @Equation338 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law338) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law338) (by native_decide) v.1 v.2
    ((@Law338.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 339 takes them (10 nodes). -/
def ordS8R164_Law339 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 339. -/
theorem noS8R164_Law339 : ∀ v : Magma.tup8R164,
    ¬ @Equation339 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law339) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law339) (by native_decide) v.1 v.2
    ((@Law339.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 340 takes them (7 nodes). -/
def ordS8R164_Law340 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 340. -/
theorem noS8R164_Law340 : ∀ v : Magma.tup8R164,
    ¬ @Equation340 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law340) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law340) (by native_decide) v.1 v.2
    ((@Law340.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 341 takes them (6 nodes). -/
def ordS8R164_Law341 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 341. -/
theorem noS8R164_Law341 : ∀ v : Magma.tup8R164,
    ¬ @Equation341 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law341) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law341) (by native_decide) v.1 v.2
    ((@Law341.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 342 takes them (6 nodes). -/
def ordS8R164_Law342 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 342. -/
theorem noS8R164_Law342 : ∀ v : Magma.tup8R164,
    ¬ @Equation342 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law342) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law342) (by native_decide) v.1 v.2
    ((@Law342.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 343 takes them (10 nodes). -/
def ordS8R164_Law343 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 343. -/
theorem noS8R164_Law343 : ∀ v : Magma.tup8R164,
    ¬ @Equation343 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law343) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law343) (by native_decide) v.1 v.2
    ((@Law343.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 344 takes them (6 nodes). -/
def ordS8R164_Law344 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 344. -/
theorem noS8R164_Law344 : ∀ v : Magma.tup8R164,
    ¬ @Equation344 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law344) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law344) (by native_decide) v.1 v.2
    ((@Law344.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 345 takes them (6 nodes). -/
def ordS8R164_Law345 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 345. -/
theorem noS8R164_Law345 : ∀ v : Magma.tup8R164,
    ¬ @Equation345 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law345) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law345) (by native_decide) v.1 v.2
    ((@Law345.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 346 takes them (7 nodes). -/
def ordS8R164_Law346 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 346. -/
theorem noS8R164_Law346 : ∀ v : Magma.tup8R164,
    ¬ @Equation346 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law346) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law346) (by native_decide) v.1 v.2
    ((@Law346.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 347 takes them (10 nodes). -/
def ordS8R164_Law347 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 347. -/
theorem noS8R164_Law347 : ∀ v : Magma.tup8R164,
    ¬ @Equation347 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law347) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law347) (by native_decide) v.1 v.2
    ((@Law347.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 348 takes them (7 nodes). -/
def ordS8R164_Law348 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 348. -/
theorem noS8R164_Law348 : ∀ v : Magma.tup8R164,
    ¬ @Equation348 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law348) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law348) (by native_decide) v.1 v.2
    ((@Law348.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 349 takes them (6 nodes). -/
def ordS8R164_Law349 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 349. -/
theorem noS8R164_Law349 : ∀ v : Magma.tup8R164,
    ¬ @Equation349 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law349) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law349) (by native_decide) v.1 v.2
    ((@Law349.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 350 takes them (6 nodes). -/
def ordS8R164_Law350 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 350. -/
theorem noS8R164_Law350 : ∀ v : Magma.tup8R164,
    ¬ @Equation350 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law350) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law350) (by native_decide) v.1 v.2
    ((@Law350.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 351 takes them (10 nodes). -/
def ordS8R164_Law351 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 351. -/
theorem noS8R164_Law351 : ∀ v : Magma.tup8R164,
    ¬ @Equation351 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law351) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law351) (by native_decide) v.1 v.2
    ((@Law351.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 352 takes them (6 nodes). -/
def ordS8R164_Law352 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 352. -/
theorem noS8R164_Law352 : ∀ v : Magma.tup8R164,
    ¬ @Equation352 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law352) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law352) (by native_decide) v.1 v.2
    ((@Law352.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 353 takes them (6 nodes). -/
def ordS8R164_Law353 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 353. -/
theorem noS8R164_Law353 : ∀ v : Magma.tup8R164,
    ¬ @Equation353 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law353) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law353) (by native_decide) v.1 v.2
    ((@Law353.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 354 takes them (6 nodes). -/
def ordS8R164_Law354 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 354. -/
theorem noS8R164_Law354 : ∀ v : Magma.tup8R164,
    ¬ @Equation354 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law354) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law354) (by native_decide) v.1 v.2
    ((@Law354.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 355 takes them (10 nodes). -/
def ordS8R164_Law355 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 355. -/
theorem noS8R164_Law355 : ∀ v : Magma.tup8R164,
    ¬ @Equation355 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law355) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law355) (by native_decide) v.1 v.2
    ((@Law355.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 356 takes them (6 nodes). -/
def ordS8R164_Law356 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 356. -/
theorem noS8R164_Law356 : ∀ v : Magma.tup8R164,
    ¬ @Equation356 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law356) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law356) (by native_decide) v.1 v.2
    ((@Law356.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 357 takes them (6 nodes). -/
def ordS8R164_Law357 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 357. -/
theorem noS8R164_Law357 : ∀ v : Magma.tup8R164,
    ¬ @Equation357 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law357) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law357) (by native_decide) v.1 v.2
    ((@Law357.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 358 takes them (6 nodes). -/
def ordS8R164_Law358 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 358. -/
theorem noS8R164_Law358 : ∀ v : Magma.tup8R164,
    ¬ @Equation358 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law358) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law358) (by native_decide) v.1 v.2
    ((@Law358.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 361 takes them (20 nodes). -/
def ordS8R164_Law361 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 361. -/
theorem noS8R164_Law361 : ∀ v : Magma.tup8R164,
    ¬ @Equation361 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law361) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law361) (by native_decide) v.1 v.2
    ((@Law361.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 363 takes them (9 nodes). -/
def ordS8R164_Law363 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 363. -/
theorem noS8R164_Law363 : ∀ v : Magma.tup8R164,
    ¬ @Equation363 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law363) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law363) (by native_decide) v.1 v.2
    ((@Law363.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 364 takes them (12 nodes). -/
def ordS8R164_Law364 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 364. -/
theorem noS8R164_Law364 : ∀ v : Magma.tup8R164,
    ¬ @Equation364 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law364) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law364) (by native_decide) v.1 v.2
    ((@Law364.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 365 takes them (13 nodes). -/
def ordS8R164_Law365 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 365. -/
theorem noS8R164_Law365 : ∀ v : Magma.tup8R164,
    ¬ @Equation365 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law365) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law365) (by native_decide) v.1 v.2
    ((@Law365.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 366 takes them (6 nodes). -/
def ordS8R164_Law366 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 366. -/
theorem noS8R164_Law366 : ∀ v : Magma.tup8R164,
    ¬ @Equation366 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law366) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law366) (by native_decide) v.1 v.2
    ((@Law366.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 370 takes them (10 nodes). -/
def ordS8R164_Law370 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 370. -/
theorem noS8R164_Law370 : ∀ v : Magma.tup8R164,
    ¬ @Equation370 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law370) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law370) (by native_decide) v.1 v.2
    ((@Law370.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 371 takes them (12 nodes). -/
def ordS8R164_Law371 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 371. -/
theorem noS8R164_Law371 : ∀ v : Magma.tup8R164,
    ¬ @Equation371 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law371) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law371) (by native_decide) v.1 v.2
    ((@Law371.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 372 takes them (9 nodes). -/
def ordS8R164_Law372 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 372. -/
theorem noS8R164_Law372 : ∀ v : Magma.tup8R164,
    ¬ @Equation372 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law372) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law372) (by native_decide) v.1 v.2
    ((@Law372.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 373 takes them (6 nodes). -/
def ordS8R164_Law373 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 373. -/
theorem noS8R164_Law373 : ∀ v : Magma.tup8R164,
    ¬ @Equation373 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law373) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law373) (by native_decide) v.1 v.2
    ((@Law373.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 374 takes them (9 nodes). -/
def ordS8R164_Law374 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 374. -/
theorem noS8R164_Law374 : ∀ v : Magma.tup8R164,
    ¬ @Equation374 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law374) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law374) (by native_decide) v.1 v.2
    ((@Law374.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 376 takes them (9 nodes). -/
def ordS8R164_Law376 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 376. -/
theorem noS8R164_Law376 : ∀ v : Magma.tup8R164,
    ¬ @Equation376 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law376) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law376) (by native_decide) v.1 v.2
    ((@Law376.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 377 takes them (17 nodes). -/
def ordS8R164_Law377 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 377. -/
theorem noS8R164_Law377 : ∀ v : Magma.tup8R164,
    ¬ @Equation377 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law377) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law377) (by native_decide) v.1 v.2
    ((@Law377.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `79` equations. -/
theorem srch8R164_refutes_0 :
    FamilyRefutes Magma.srch8R164 [
      10, 25, 38, 39, 41, 42, 44, 45, 46, 101, 104, 106, 110, 111, 152, 153, 156, 166, 205, 208,
      214, 224, 242, 308, 309, 311, 313, 314, 317, 318, 319, 321, 322, 323, 324, 325, 327, 328,
      329, 330, 331, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347,
      348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 361, 363, 364, 365, 366, 370, 371,
      372, 373, 374, 376, 377
    ] :=
  ⟨noS8R164_Law10, noS8R164_Law25, noS8R164_Law38, noS8R164_Law39, noS8R164_Law41, noS8R164_Law42, noS8R164_Law44, noS8R164_Law45, noS8R164_Law46, noS8R164_Law101, noS8R164_Law104, noS8R164_Law106, noS8R164_Law110, noS8R164_Law111, noS8R164_Law152, noS8R164_Law153, noS8R164_Law156, noS8R164_Law166, noS8R164_Law205, noS8R164_Law208, noS8R164_Law214, noS8R164_Law224, noS8R164_Law242, noS8R164_Law308, noS8R164_Law309, noS8R164_Law311, noS8R164_Law313, noS8R164_Law314, noS8R164_Law317, noS8R164_Law318, noS8R164_Law319, noS8R164_Law321, noS8R164_Law322, noS8R164_Law323, noS8R164_Law324, noS8R164_Law325, noS8R164_Law327, noS8R164_Law328, noS8R164_Law329, noS8R164_Law330, noS8R164_Law331, noS8R164_Law333, noS8R164_Law334, noS8R164_Law335, noS8R164_Law336, noS8R164_Law337, noS8R164_Law338, noS8R164_Law339, noS8R164_Law340, noS8R164_Law341, noS8R164_Law342, noS8R164_Law343, noS8R164_Law344, noS8R164_Law345, noS8R164_Law346, noS8R164_Law347, noS8R164_Law348, noS8R164_Law349, noS8R164_Law350, noS8R164_Law351, noS8R164_Law352, noS8R164_Law353, noS8R164_Law354, noS8R164_Law355, noS8R164_Law356, noS8R164_Law357, noS8R164_Law358, noS8R164_Law361, noS8R164_Law363, noS8R164_Law364, noS8R164_Law365, noS8R164_Law366, noS8R164_Law370, noS8R164_Law371, noS8R164_Law372, noS8R164_Law373, noS8R164_Law374, noS8R164_Law376, noS8R164_Law377⟩
