import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 13 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `84` equations here, 605 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4172 takes them (8 nodes). -/
def ordS8R164_Law4172 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4172. -/
theorem noS8R164_Law4172 : ∀ v : Magma.tup8R164,
    ¬ @Equation4172 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4172) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4172) (by native_decide) v.1 v.2
    ((@Law4172.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4173 takes them (6 nodes). -/
def ordS8R164_Law4173 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4173. -/
theorem noS8R164_Law4173 : ∀ v : Magma.tup8R164,
    ¬ @Equation4173 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4173) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4173) (by native_decide) v.1 v.2
    ((@Law4173.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4174 takes them (7 nodes). -/
def ordS8R164_Law4174 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4174. -/
theorem noS8R164_Law4174 : ∀ v : Magma.tup8R164,
    ¬ @Equation4174 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4174) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4174) (by native_decide) v.1 v.2
    ((@Law4174.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4175 takes them (13 nodes). -/
def ordS8R164_Law4175 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4175. -/
theorem noS8R164_Law4175 : ∀ v : Magma.tup8R164,
    ¬ @Equation4175 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4175) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4175) (by native_decide) v.1 v.2
    ((@Law4175.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4177 takes them (6 nodes). -/
def ordS8R164_Law4177 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4177. -/
theorem noS8R164_Law4177 : ∀ v : Magma.tup8R164,
    ¬ @Equation4177 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4177) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4177) (by native_decide) v.1 v.2
    ((@Law4177.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4178 takes them (7 nodes). -/
def ordS8R164_Law4178 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4178. -/
theorem noS8R164_Law4178 : ∀ v : Magma.tup8R164,
    ¬ @Equation4178 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4178) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4178) (by native_decide) v.1 v.2
    ((@Law4178.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4179 takes them (10 nodes). -/
def ordS8R164_Law4179 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4179. -/
theorem noS8R164_Law4179 : ∀ v : Magma.tup8R164,
    ¬ @Equation4179 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4179) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4179) (by native_decide) v.1 v.2
    ((@Law4179.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4180 takes them (7 nodes). -/
def ordS8R164_Law4180 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4180. -/
theorem noS8R164_Law4180 : ∀ v : Magma.tup8R164,
    ¬ @Equation4180 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4180) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4180) (by native_decide) v.1 v.2
    ((@Law4180.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4181 takes them (6 nodes). -/
def ordS8R164_Law4181 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4181. -/
theorem noS8R164_Law4181 : ∀ v : Magma.tup8R164,
    ¬ @Equation4181 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4181) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4181) (by native_decide) v.1 v.2
    ((@Law4181.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4183 takes them (10 nodes). -/
def ordS8R164_Law4183 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4183. -/
theorem noS8R164_Law4183 : ∀ v : Magma.tup8R164,
    ¬ @Equation4183 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4183) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4183) (by native_decide) v.1 v.2
    ((@Law4183.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4184 takes them (7 nodes). -/
def ordS8R164_Law4184 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4184. -/
theorem noS8R164_Law4184 : ∀ v : Magma.tup8R164,
    ¬ @Equation4184 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4184) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4184) (by native_decide) v.1 v.2
    ((@Law4184.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4185 takes them (6 nodes). -/
def ordS8R164_Law4185 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4185. -/
theorem noS8R164_Law4185 : ∀ v : Magma.tup8R164,
    ¬ @Equation4185 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4185) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4185) (by native_decide) v.1 v.2
    ((@Law4185.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4186 takes them (7 nodes). -/
def ordS8R164_Law4186 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4186. -/
theorem noS8R164_Law4186 : ∀ v : Magma.tup8R164,
    ¬ @Equation4186 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4186) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4186) (by native_decide) v.1 v.2
    ((@Law4186.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4187 takes them (10 nodes). -/
def ordS8R164_Law4187 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4187. -/
theorem noS8R164_Law4187 : ∀ v : Magma.tup8R164,
    ¬ @Equation4187 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4187) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4187) (by native_decide) v.1 v.2
    ((@Law4187.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4188 takes them (7 nodes). -/
def ordS8R164_Law4188 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4188. -/
theorem noS8R164_Law4188 : ∀ v : Magma.tup8R164,
    ¬ @Equation4188 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4188) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4188) (by native_decide) v.1 v.2
    ((@Law4188.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4189 takes them (7 nodes). -/
def ordS8R164_Law4189 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4189. -/
theorem noS8R164_Law4189 : ∀ v : Magma.tup8R164,
    ¬ @Equation4189 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4189) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4189) (by native_decide) v.1 v.2
    ((@Law4189.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4190 takes them (6 nodes). -/
def ordS8R164_Law4190 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4190. -/
theorem noS8R164_Law4190 : ∀ v : Magma.tup8R164,
    ¬ @Equation4190 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4190) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4190) (by native_decide) v.1 v.2
    ((@Law4190.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4191 takes them (6 nodes). -/
def ordS8R164_Law4191 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4191. -/
theorem noS8R164_Law4191 : ∀ v : Magma.tup8R164,
    ¬ @Equation4191 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4191) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4191) (by native_decide) v.1 v.2
    ((@Law4191.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4192 takes them (11 nodes). -/
def ordS8R164_Law4192 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4192. -/
theorem noS8R164_Law4192 : ∀ v : Magma.tup8R164,
    ¬ @Equation4192 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4192) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4192) (by native_decide) v.1 v.2
    ((@Law4192.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4193 takes them (6 nodes). -/
def ordS8R164_Law4193 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4193. -/
theorem noS8R164_Law4193 : ∀ v : Magma.tup8R164,
    ¬ @Equation4193 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4193) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4193) (by native_decide) v.1 v.2
    ((@Law4193.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4194 takes them (6 nodes). -/
def ordS8R164_Law4194 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4194. -/
theorem noS8R164_Law4194 : ∀ v : Magma.tup8R164,
    ¬ @Equation4194 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4194) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4194) (by native_decide) v.1 v.2
    ((@Law4194.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4195 takes them (7 nodes). -/
def ordS8R164_Law4195 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4195. -/
theorem noS8R164_Law4195 : ∀ v : Magma.tup8R164,
    ¬ @Equation4195 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4195) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4195) (by native_decide) v.1 v.2
    ((@Law4195.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4196 takes them (10 nodes). -/
def ordS8R164_Law4196 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4196. -/
theorem noS8R164_Law4196 : ∀ v : Magma.tup8R164,
    ¬ @Equation4196 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4196) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4196) (by native_decide) v.1 v.2
    ((@Law4196.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4198 takes them (6 nodes). -/
def ordS8R164_Law4198 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4198. -/
theorem noS8R164_Law4198 : ∀ v : Magma.tup8R164,
    ¬ @Equation4198 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4198) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4198) (by native_decide) v.1 v.2
    ((@Law4198.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4199 takes them (6 nodes). -/
def ordS8R164_Law4199 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4199. -/
theorem noS8R164_Law4199 : ∀ v : Magma.tup8R164,
    ¬ @Equation4199 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4199) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4199) (by native_decide) v.1 v.2
    ((@Law4199.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4201 takes them (6 nodes). -/
def ordS8R164_Law4201 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4201. -/
theorem noS8R164_Law4201 : ∀ v : Magma.tup8R164,
    ¬ @Equation4201 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4201) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4201) (by native_decide) v.1 v.2
    ((@Law4201.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4202 takes them (6 nodes). -/
def ordS8R164_Law4202 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4202. -/
theorem noS8R164_Law4202 : ∀ v : Magma.tup8R164,
    ¬ @Equation4202 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4202) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4202) (by native_decide) v.1 v.2
    ((@Law4202.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4203 takes them (6 nodes). -/
def ordS8R164_Law4203 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4203. -/
theorem noS8R164_Law4203 : ∀ v : Magma.tup8R164,
    ¬ @Equation4203 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4203) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4203) (by native_decide) v.1 v.2
    ((@Law4203.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4204 takes them (10 nodes). -/
def ordS8R164_Law4204 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4204. -/
theorem noS8R164_Law4204 : ∀ v : Magma.tup8R164,
    ¬ @Equation4204 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4204) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4204) (by native_decide) v.1 v.2
    ((@Law4204.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4205 takes them (6 nodes). -/
def ordS8R164_Law4205 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4205. -/
theorem noS8R164_Law4205 : ∀ v : Magma.tup8R164,
    ¬ @Equation4205 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4205) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4205) (by native_decide) v.1 v.2
    ((@Law4205.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4206 takes them (6 nodes). -/
def ordS8R164_Law4206 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4206. -/
theorem noS8R164_Law4206 : ∀ v : Magma.tup8R164,
    ¬ @Equation4206 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4206) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4206) (by native_decide) v.1 v.2
    ((@Law4206.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4207 takes them (6 nodes). -/
def ordS8R164_Law4207 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4207. -/
theorem noS8R164_Law4207 : ∀ v : Magma.tup8R164,
    ¬ @Equation4207 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4207) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4207) (by native_decide) v.1 v.2
    ((@Law4207.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4208 takes them (7 nodes). -/
def ordS8R164_Law4208 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4208. -/
theorem noS8R164_Law4208 : ∀ v : Magma.tup8R164,
    ¬ @Equation4208 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4208) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4208) (by native_decide) v.1 v.2
    ((@Law4208.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4209 takes them (10 nodes). -/
def ordS8R164_Law4209 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4209. -/
theorem noS8R164_Law4209 : ∀ v : Magma.tup8R164,
    ¬ @Equation4209 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4209) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4209) (by native_decide) v.1 v.2
    ((@Law4209.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4211 takes them (6 nodes). -/
def ordS8R164_Law4211 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4211. -/
theorem noS8R164_Law4211 : ∀ v : Magma.tup8R164,
    ¬ @Equation4211 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4211) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4211) (by native_decide) v.1 v.2
    ((@Law4211.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4212 takes them (7 nodes). -/
def ordS8R164_Law4212 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4212. -/
theorem noS8R164_Law4212 : ∀ v : Magma.tup8R164,
    ¬ @Equation4212 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4212) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4212) (by native_decide) v.1 v.2
    ((@Law4212.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4213 takes them (10 nodes). -/
def ordS8R164_Law4213 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4213. -/
theorem noS8R164_Law4213 : ∀ v : Magma.tup8R164,
    ¬ @Equation4213 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4213) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4213) (by native_decide) v.1 v.2
    ((@Law4213.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4214 takes them (7 nodes). -/
def ordS8R164_Law4214 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4214. -/
theorem noS8R164_Law4214 : ∀ v : Magma.tup8R164,
    ¬ @Equation4214 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4214) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4214) (by native_decide) v.1 v.2
    ((@Law4214.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4215 takes them (6 nodes). -/
def ordS8R164_Law4215 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4215. -/
theorem noS8R164_Law4215 : ∀ v : Magma.tup8R164,
    ¬ @Equation4215 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4215) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4215) (by native_decide) v.1 v.2
    ((@Law4215.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4217 takes them (10 nodes). -/
def ordS8R164_Law4217 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4217. -/
theorem noS8R164_Law4217 : ∀ v : Magma.tup8R164,
    ¬ @Equation4217 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4217) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4217) (by native_decide) v.1 v.2
    ((@Law4217.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4218 takes them (7 nodes). -/
def ordS8R164_Law4218 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4218. -/
theorem noS8R164_Law4218 : ∀ v : Magma.tup8R164,
    ¬ @Equation4218 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4218) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4218) (by native_decide) v.1 v.2
    ((@Law4218.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4219 takes them (6 nodes). -/
def ordS8R164_Law4219 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4219. -/
theorem noS8R164_Law4219 : ∀ v : Magma.tup8R164,
    ¬ @Equation4219 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4219) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4219) (by native_decide) v.1 v.2
    ((@Law4219.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4220 takes them (7 nodes). -/
def ordS8R164_Law4220 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4220. -/
theorem noS8R164_Law4220 : ∀ v : Magma.tup8R164,
    ¬ @Equation4220 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4220) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4220) (by native_decide) v.1 v.2
    ((@Law4220.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4221 takes them (10 nodes). -/
def ordS8R164_Law4221 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4221. -/
theorem noS8R164_Law4221 : ∀ v : Magma.tup8R164,
    ¬ @Equation4221 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4221) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4221) (by native_decide) v.1 v.2
    ((@Law4221.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4222 takes them (7 nodes). -/
def ordS8R164_Law4222 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4222. -/
theorem noS8R164_Law4222 : ∀ v : Magma.tup8R164,
    ¬ @Equation4222 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4222) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4222) (by native_decide) v.1 v.2
    ((@Law4222.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4223 takes them (7 nodes). -/
def ordS8R164_Law4223 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4223. -/
theorem noS8R164_Law4223 : ∀ v : Magma.tup8R164,
    ¬ @Equation4223 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4223) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4223) (by native_decide) v.1 v.2
    ((@Law4223.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4224 takes them (6 nodes). -/
def ordS8R164_Law4224 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4224. -/
theorem noS8R164_Law4224 : ∀ v : Magma.tup8R164,
    ¬ @Equation4224 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4224) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4224) (by native_decide) v.1 v.2
    ((@Law4224.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4225 takes them (6 nodes). -/
def ordS8R164_Law4225 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4225. -/
theorem noS8R164_Law4225 : ∀ v : Magma.tup8R164,
    ¬ @Equation4225 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4225) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4225) (by native_decide) v.1 v.2
    ((@Law4225.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4227 takes them (6 nodes). -/
def ordS8R164_Law4227 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4227. -/
theorem noS8R164_Law4227 : ∀ v : Magma.tup8R164,
    ¬ @Equation4227 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4227) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4227) (by native_decide) v.1 v.2
    ((@Law4227.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4228 takes them (6 nodes). -/
def ordS8R164_Law4228 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4228. -/
theorem noS8R164_Law4228 : ∀ v : Magma.tup8R164,
    ¬ @Equation4228 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4228) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4228) (by native_decide) v.1 v.2
    ((@Law4228.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4230 takes them (10 nodes). -/
def ordS8R164_Law4230 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4230. -/
theorem noS8R164_Law4230 : ∀ v : Magma.tup8R164,
    ¬ @Equation4230 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4230) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4230) (by native_decide) v.1 v.2
    ((@Law4230.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4231 takes them (7 nodes). -/
def ordS8R164_Law4231 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4231. -/
theorem noS8R164_Law4231 : ∀ v : Magma.tup8R164,
    ¬ @Equation4231 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4231) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4231) (by native_decide) v.1 v.2
    ((@Law4231.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4232 takes them (6 nodes). -/
def ordS8R164_Law4232 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4232. -/
theorem noS8R164_Law4232 : ∀ v : Magma.tup8R164,
    ¬ @Equation4232 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4232) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4232) (by native_decide) v.1 v.2
    ((@Law4232.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4233 takes them (6 nodes). -/
def ordS8R164_Law4233 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4233. -/
theorem noS8R164_Law4233 : ∀ v : Magma.tup8R164,
    ¬ @Equation4233 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4233) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4233) (by native_decide) v.1 v.2
    ((@Law4233.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4234 takes them (10 nodes). -/
def ordS8R164_Law4234 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4234. -/
theorem noS8R164_Law4234 : ∀ v : Magma.tup8R164,
    ¬ @Equation4234 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4234) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4234) (by native_decide) v.1 v.2
    ((@Law4234.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4235 takes them (6 nodes). -/
def ordS8R164_Law4235 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4235. -/
theorem noS8R164_Law4235 : ∀ v : Magma.tup8R164,
    ¬ @Equation4235 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4235) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4235) (by native_decide) v.1 v.2
    ((@Law4235.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4236 takes them (6 nodes). -/
def ordS8R164_Law4236 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4236. -/
theorem noS8R164_Law4236 : ∀ v : Magma.tup8R164,
    ¬ @Equation4236 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4236) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4236) (by native_decide) v.1 v.2
    ((@Law4236.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4237 takes them (6 nodes). -/
def ordS8R164_Law4237 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4237. -/
theorem noS8R164_Law4237 : ∀ v : Magma.tup8R164,
    ¬ @Equation4237 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4237) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4237) (by native_decide) v.1 v.2
    ((@Law4237.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4238 takes them (10 nodes). -/
def ordS8R164_Law4238 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4238. -/
theorem noS8R164_Law4238 : ∀ v : Magma.tup8R164,
    ¬ @Equation4238 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4238) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4238) (by native_decide) v.1 v.2
    ((@Law4238.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4239 takes them (6 nodes). -/
def ordS8R164_Law4239 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4239. -/
theorem noS8R164_Law4239 : ∀ v : Magma.tup8R164,
    ¬ @Equation4239 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4239) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4239) (by native_decide) v.1 v.2
    ((@Law4239.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4240 takes them (6 nodes). -/
def ordS8R164_Law4240 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4240. -/
theorem noS8R164_Law4240 : ∀ v : Magma.tup8R164,
    ¬ @Equation4240 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4240) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4240) (by native_decide) v.1 v.2
    ((@Law4240.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4241 takes them (6 nodes). -/
def ordS8R164_Law4241 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4241. -/
theorem noS8R164_Law4241 : ∀ v : Magma.tup8R164,
    ¬ @Equation4241 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4241) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4241) (by native_decide) v.1 v.2
    ((@Law4241.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4242 takes them (6 nodes). -/
def ordS8R164_Law4242 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4242. -/
theorem noS8R164_Law4242 : ∀ v : Magma.tup8R164,
    ¬ @Equation4242 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4242) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4242) (by native_decide) v.1 v.2
    ((@Law4242.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (10 nodes). -/
def ordS8R164_Law4243 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4243. -/
theorem noS8R164_Law4243 : ∀ v : Magma.tup8R164,
    ¬ @Equation4243 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4244 takes them (6 nodes). -/
def ordS8R164_Law4244 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4244. -/
theorem noS8R164_Law4244 : ∀ v : Magma.tup8R164,
    ¬ @Equation4244 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4244) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4244) (by native_decide) v.1 v.2
    ((@Law4244.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4245 takes them (6 nodes). -/
def ordS8R164_Law4245 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4245. -/
theorem noS8R164_Law4245 : ∀ v : Magma.tup8R164,
    ¬ @Equation4245 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4245) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4245) (by native_decide) v.1 v.2
    ((@Law4245.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4246 takes them (6 nodes). -/
def ordS8R164_Law4246 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4246. -/
theorem noS8R164_Law4246 : ∀ v : Magma.tup8R164,
    ¬ @Equation4246 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4246) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4246) (by native_decide) v.1 v.2
    ((@Law4246.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4247 takes them (7 nodes). -/
def ordS8R164_Law4247 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4247. -/
theorem noS8R164_Law4247 : ∀ v : Magma.tup8R164,
    ¬ @Equation4247 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4247) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4247) (by native_decide) v.1 v.2
    ((@Law4247.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4248 takes them (10 nodes). -/
def ordS8R164_Law4248 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4248. -/
theorem noS8R164_Law4248 : ∀ v : Magma.tup8R164,
    ¬ @Equation4248 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4248) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4248) (by native_decide) v.1 v.2
    ((@Law4248.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4249 takes them (7 nodes). -/
def ordS8R164_Law4249 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4249. -/
theorem noS8R164_Law4249 : ∀ v : Magma.tup8R164,
    ¬ @Equation4249 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4249) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4249) (by native_decide) v.1 v.2
    ((@Law4249.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4250 takes them (7 nodes). -/
def ordS8R164_Law4250 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4250. -/
theorem noS8R164_Law4250 : ∀ v : Magma.tup8R164,
    ¬ @Equation4250 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4250) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4250) (by native_decide) v.1 v.2
    ((@Law4250.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4251 takes them (6 nodes). -/
def ordS8R164_Law4251 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4251. -/
theorem noS8R164_Law4251 : ∀ v : Magma.tup8R164,
    ¬ @Equation4251 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4251) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4251) (by native_decide) v.1 v.2
    ((@Law4251.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4252 takes them (6 nodes). -/
def ordS8R164_Law4252 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4252. -/
theorem noS8R164_Law4252 : ∀ v : Magma.tup8R164,
    ¬ @Equation4252 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4252) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4252) (by native_decide) v.1 v.2
    ((@Law4252.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4253 takes them (10 nodes). -/
def ordS8R164_Law4253 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4253. -/
theorem noS8R164_Law4253 : ∀ v : Magma.tup8R164,
    ¬ @Equation4253 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4253) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4253) (by native_decide) v.1 v.2
    ((@Law4253.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4254 takes them (6 nodes). -/
def ordS8R164_Law4254 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4254. -/
theorem noS8R164_Law4254 : ∀ v : Magma.tup8R164,
    ¬ @Equation4254 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4254) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4254) (by native_decide) v.1 v.2
    ((@Law4254.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4255 takes them (6 nodes). -/
def ordS8R164_Law4255 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4255. -/
theorem noS8R164_Law4255 : ∀ v : Magma.tup8R164,
    ¬ @Equation4255 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4255) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4255) (by native_decide) v.1 v.2
    ((@Law4255.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4256 takes them (6 nodes). -/
def ordS8R164_Law4256 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4256. -/
theorem noS8R164_Law4256 : ∀ v : Magma.tup8R164,
    ¬ @Equation4256 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4256) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4256) (by native_decide) v.1 v.2
    ((@Law4256.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4257 takes them (6 nodes). -/
def ordS8R164_Law4257 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4257. -/
theorem noS8R164_Law4257 : ∀ v : Magma.tup8R164,
    ¬ @Equation4257 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4257) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4257) (by native_decide) v.1 v.2
    ((@Law4257.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4258 takes them (10 nodes). -/
def ordS8R164_Law4258 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4258. -/
theorem noS8R164_Law4258 : ∀ v : Magma.tup8R164,
    ¬ @Equation4258 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4258) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4258) (by native_decide) v.1 v.2
    ((@Law4258.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4259 takes them (6 nodes). -/
def ordS8R164_Law4259 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4259. -/
theorem noS8R164_Law4259 : ∀ v : Magma.tup8R164,
    ¬ @Equation4259 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4259) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4259) (by native_decide) v.1 v.2
    ((@Law4259.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4260 takes them (6 nodes). -/
def ordS8R164_Law4260 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4260. -/
theorem noS8R164_Law4260 : ∀ v : Magma.tup8R164,
    ¬ @Equation4260 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4260) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4260) (by native_decide) v.1 v.2
    ((@Law4260.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4261 takes them (6 nodes). -/
def ordS8R164_Law4261 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4261. -/
theorem noS8R164_Law4261 : ∀ v : Magma.tup8R164,
    ¬ @Equation4261 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4261) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4261) (by native_decide) v.1 v.2
    ((@Law4261.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4262 takes them (6 nodes). -/
def ordS8R164_Law4262 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4262. -/
theorem noS8R164_Law4262 : ∀ v : Magma.tup8R164,
    ¬ @Equation4262 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4262) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4262) (by native_decide) v.1 v.2
    ((@Law4262.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4263 takes them (10 nodes). -/
def ordS8R164_Law4263 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4263. -/
theorem noS8R164_Law4263 : ∀ v : Magma.tup8R164,
    ¬ @Equation4263 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4263) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4263) (by native_decide) v.1 v.2
    ((@Law4263.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `84` equations. -/
theorem srch8R164_refutes_12 :
    FamilyRefutes Magma.srch8R164 [
      4172, 4173, 4174, 4175, 4177, 4178, 4179, 4180, 4181, 4183, 4184, 4185, 4186, 4187, 4188,
      4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4198, 4199, 4201, 4202, 4203, 4204, 4205,
      4206, 4207, 4208, 4209, 4211, 4212, 4213, 4214, 4215, 4217, 4218, 4219, 4220, 4221, 4222,
      4223, 4224, 4225, 4227, 4228, 4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239,
      4240, 4241, 4242, 4243, 4244, 4245, 4246, 4247, 4248, 4249, 4250, 4251, 4252, 4253, 4254,
      4255, 4256, 4257, 4258, 4259, 4260, 4261, 4262, 4263
    ] :=
  ⟨noS8R164_Law4172, noS8R164_Law4173, noS8R164_Law4174, noS8R164_Law4175, noS8R164_Law4177, noS8R164_Law4178, noS8R164_Law4179, noS8R164_Law4180, noS8R164_Law4181, noS8R164_Law4183, noS8R164_Law4184, noS8R164_Law4185, noS8R164_Law4186, noS8R164_Law4187, noS8R164_Law4188, noS8R164_Law4189, noS8R164_Law4190, noS8R164_Law4191, noS8R164_Law4192, noS8R164_Law4193, noS8R164_Law4194, noS8R164_Law4195, noS8R164_Law4196, noS8R164_Law4198, noS8R164_Law4199, noS8R164_Law4201, noS8R164_Law4202, noS8R164_Law4203, noS8R164_Law4204, noS8R164_Law4205, noS8R164_Law4206, noS8R164_Law4207, noS8R164_Law4208, noS8R164_Law4209, noS8R164_Law4211, noS8R164_Law4212, noS8R164_Law4213, noS8R164_Law4214, noS8R164_Law4215, noS8R164_Law4217, noS8R164_Law4218, noS8R164_Law4219, noS8R164_Law4220, noS8R164_Law4221, noS8R164_Law4222, noS8R164_Law4223, noS8R164_Law4224, noS8R164_Law4225, noS8R164_Law4227, noS8R164_Law4228, noS8R164_Law4230, noS8R164_Law4231, noS8R164_Law4232, noS8R164_Law4233, noS8R164_Law4234, noS8R164_Law4235, noS8R164_Law4236, noS8R164_Law4237, noS8R164_Law4238, noS8R164_Law4239, noS8R164_Law4240, noS8R164_Law4241, noS8R164_Law4242, noS8R164_Law4243, noS8R164_Law4244, noS8R164_Law4245, noS8R164_Law4246, noS8R164_Law4247, noS8R164_Law4248, noS8R164_Law4249, noS8R164_Law4250, noS8R164_Law4251, noS8R164_Law4252, noS8R164_Law4253, noS8R164_Law4254, noS8R164_Law4255, noS8R164_Law4256, noS8R164_Law4257, noS8R164_Law4258, noS8R164_Law4259, noS8R164_Law4260, noS8R164_Law4261, noS8R164_Law4262, noS8R164_Law4263⟩
