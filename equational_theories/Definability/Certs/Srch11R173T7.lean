import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 8 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 289 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4155 takes them (3 nodes). -/
def ordS11R173_Law4155 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4155. -/
theorem noS11R173_Law4155 : ∀ v : Magma.tup11R173,
    ¬ @Equation4155 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4155) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4155) (by native_decide) v.1 v.2
    ((@Law4155.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (3 nodes). -/
def ordS11R173_Law4158 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4158. -/
theorem noS11R173_Law4158 : ∀ v : Magma.tup11R173,
    ¬ @Equation4158 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4161 takes them (3 nodes). -/
def ordS11R173_Law4161 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4161. -/
theorem noS11R173_Law4161 : ∀ v : Magma.tup11R173,
    ¬ @Equation4161 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4161) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4161) (by native_decide) v.1 v.2
    ((@Law4161.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4165 takes them (3 nodes). -/
def ordS11R173_Law4165 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4165. -/
theorem noS11R173_Law4165 : ∀ v : Magma.tup11R173,
    ¬ @Equation4165 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4165) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4165) (by native_decide) v.1 v.2
    ((@Law4165.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4168 takes them (3 nodes). -/
def ordS11R173_Law4168 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4168. -/
theorem noS11R173_Law4168 : ∀ v : Magma.tup11R173,
    ¬ @Equation4168 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4168) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4168) (by native_decide) v.1 v.2
    ((@Law4168.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4171 takes them (3 nodes). -/
def ordS11R173_Law4171 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4171. -/
theorem noS11R173_Law4171 : ∀ v : Magma.tup11R173,
    ¬ @Equation4171 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4171) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4171) (by native_decide) v.1 v.2
    ((@Law4171.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4175 takes them (3 nodes). -/
def ordS11R173_Law4175 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4175. -/
theorem noS11R173_Law4175 : ∀ v : Magma.tup11R173,
    ¬ @Equation4175 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4175) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4175) (by native_decide) v.1 v.2
    ((@Law4175.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4179 takes them (3 nodes). -/
def ordS11R173_Law4179 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4179. -/
theorem noS11R173_Law4179 : ∀ v : Magma.tup11R173,
    ¬ @Equation4179 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4179) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4179) (by native_decide) v.1 v.2
    ((@Law4179.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4183 takes them (3 nodes). -/
def ordS11R173_Law4183 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4183. -/
theorem noS11R173_Law4183 : ∀ v : Magma.tup11R173,
    ¬ @Equation4183 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4183) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4183) (by native_decide) v.1 v.2
    ((@Law4183.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4187 takes them (3 nodes). -/
def ordS11R173_Law4187 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4187. -/
theorem noS11R173_Law4187 : ∀ v : Magma.tup11R173,
    ¬ @Equation4187 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4187) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4187) (by native_decide) v.1 v.2
    ((@Law4187.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4192 takes them (3 nodes). -/
def ordS11R173_Law4192 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4192. -/
theorem noS11R173_Law4192 : ∀ v : Magma.tup11R173,
    ¬ @Equation4192 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4192) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4192) (by native_decide) v.1 v.2
    ((@Law4192.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4196 takes them (3 nodes). -/
def ordS11R173_Law4196 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4196. -/
theorem noS11R173_Law4196 : ∀ v : Magma.tup11R173,
    ¬ @Equation4196 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4196) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4196) (by native_decide) v.1 v.2
    ((@Law4196.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (3 nodes). -/
def ordS11R173_Law4200 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4200. -/
theorem noS11R173_Law4200 : ∀ v : Magma.tup11R173,
    ¬ @Equation4200 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4204 takes them (3 nodes). -/
def ordS11R173_Law4204 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4204. -/
theorem noS11R173_Law4204 : ∀ v : Magma.tup11R173,
    ¬ @Equation4204 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4204) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4204) (by native_decide) v.1 v.2
    ((@Law4204.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4209 takes them (3 nodes). -/
def ordS11R173_Law4209 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4209. -/
theorem noS11R173_Law4209 : ∀ v : Magma.tup11R173,
    ¬ @Equation4209 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4209) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4209) (by native_decide) v.1 v.2
    ((@Law4209.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4213 takes them (3 nodes). -/
def ordS11R173_Law4213 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4213. -/
theorem noS11R173_Law4213 : ∀ v : Magma.tup11R173,
    ¬ @Equation4213 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4213) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4213) (by native_decide) v.1 v.2
    ((@Law4213.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4217 takes them (3 nodes). -/
def ordS11R173_Law4217 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4217. -/
theorem noS11R173_Law4217 : ∀ v : Magma.tup11R173,
    ¬ @Equation4217 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4217) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4217) (by native_decide) v.1 v.2
    ((@Law4217.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4221 takes them (3 nodes). -/
def ordS11R173_Law4221 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4221. -/
theorem noS11R173_Law4221 : ∀ v : Magma.tup11R173,
    ¬ @Equation4221 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4221) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4221) (by native_decide) v.1 v.2
    ((@Law4221.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4226 takes them (3 nodes). -/
def ordS11R173_Law4226 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4226. -/
theorem noS11R173_Law4226 : ∀ v : Magma.tup11R173,
    ¬ @Equation4226 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4226) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4226) (by native_decide) v.1 v.2
    ((@Law4226.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4230 takes them (3 nodes). -/
def ordS11R173_Law4230 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4230. -/
theorem noS11R173_Law4230 : ∀ v : Magma.tup11R173,
    ¬ @Equation4230 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4230) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4230) (by native_decide) v.1 v.2
    ((@Law4230.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4234 takes them (3 nodes). -/
def ordS11R173_Law4234 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4234. -/
theorem noS11R173_Law4234 : ∀ v : Magma.tup11R173,
    ¬ @Equation4234 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4234) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4234) (by native_decide) v.1 v.2
    ((@Law4234.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4238 takes them (3 nodes). -/
def ordS11R173_Law4238 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4238. -/
theorem noS11R173_Law4238 : ∀ v : Magma.tup11R173,
    ¬ @Equation4238 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4238) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4238) (by native_decide) v.1 v.2
    ((@Law4238.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (3 nodes). -/
def ordS11R173_Law4243 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4243. -/
theorem noS11R173_Law4243 : ∀ v : Magma.tup11R173,
    ¬ @Equation4243 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4248 takes them (3 nodes). -/
def ordS11R173_Law4248 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4248. -/
theorem noS11R173_Law4248 : ∀ v : Magma.tup11R173,
    ¬ @Equation4248 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4248) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4248) (by native_decide) v.1 v.2
    ((@Law4248.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4253 takes them (3 nodes). -/
def ordS11R173_Law4253 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4253. -/
theorem noS11R173_Law4253 : ∀ v : Magma.tup11R173,
    ¬ @Equation4253 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4253) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4253) (by native_decide) v.1 v.2
    ((@Law4253.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4258 takes them (3 nodes). -/
def ordS11R173_Law4258 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4258. -/
theorem noS11R173_Law4258 : ∀ v : Magma.tup11R173,
    ¬ @Equation4258 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4258) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4258) (by native_decide) v.1 v.2
    ((@Law4258.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4268 takes them (3 nodes). -/
def ordS11R173_Law4268 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4268. -/
theorem noS11R173_Law4268 : ∀ v : Magma.tup11R173,
    ¬ @Equation4268 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4268) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4268) (by native_decide) v.1 v.2
    ((@Law4268.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4269 takes them (4 nodes). -/
def ordS11R173_Law4269 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4269. -/
theorem noS11R173_Law4269 : ∀ v : Magma.tup11R173,
    ¬ @Equation4269 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4269) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4269) (by native_decide) v.1 v.2
    ((@Law4269.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4270 takes them (3 nodes). -/
def ordS11R173_Law4270 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4270. -/
theorem noS11R173_Law4270 : ∀ v : Magma.tup11R173,
    ¬ @Equation4270 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4270) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4270) (by native_decide) v.1 v.2
    ((@Law4270.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4271 takes them (3 nodes). -/
def ordS11R173_Law4271 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4271. -/
theorem noS11R173_Law4271 : ∀ v : Magma.tup11R173,
    ¬ @Equation4271 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4271) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4271) (by native_decide) v.1 v.2
    ((@Law4271.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4272 takes them (3 nodes). -/
def ordS11R173_Law4272 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4272. -/
theorem noS11R173_Law4272 : ∀ v : Magma.tup11R173,
    ¬ @Equation4272 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4272) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4272) (by native_decide) v.1 v.2
    ((@Law4272.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4278 takes them (3 nodes). -/
def ordS11R173_Law4278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4278. -/
theorem noS11R173_Law4278 : ∀ v : Magma.tup11R173,
    ¬ @Equation4278 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4278) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4278) (by native_decide) v.1 v.2
    ((@Law4278.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4282 takes them (3 nodes). -/
def ordS11R173_Law4282 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4282. -/
theorem noS11R173_Law4282 : ∀ v : Magma.tup11R173,
    ¬ @Equation4282 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4282) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4282) (by native_decide) v.1 v.2
    ((@Law4282.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4284 takes them (4 nodes). -/
def ordS11R173_Law4284 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4284. -/
theorem noS11R173_Law4284 : ∀ v : Magma.tup11R173,
    ¬ @Equation4284 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4284) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4284) (by native_decide) v.1 v.2
    ((@Law4284.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4285 takes them (3 nodes). -/
def ordS11R173_Law4285 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4285. -/
theorem noS11R173_Law4285 : ∀ v : Magma.tup11R173,
    ¬ @Equation4285 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4285) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4285) (by native_decide) v.1 v.2
    ((@Law4285.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4286 takes them (3 nodes). -/
def ordS11R173_Law4286 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4286. -/
theorem noS11R173_Law4286 : ∀ v : Magma.tup11R173,
    ¬ @Equation4286 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4286) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4286) (by native_decide) v.1 v.2
    ((@Law4286.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4287 takes them (4 nodes). -/
def ordS11R173_Law4287 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4287. -/
theorem noS11R173_Law4287 : ∀ v : Magma.tup11R173,
    ¬ @Equation4287 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4287) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4287) (by native_decide) v.1 v.2
    ((@Law4287.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4288 takes them (3 nodes). -/
def ordS11R173_Law4288 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4288. -/
theorem noS11R173_Law4288 : ∀ v : Magma.tup11R173,
    ¬ @Equation4288 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4288) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4288) (by native_decide) v.1 v.2
    ((@Law4288.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4289 takes them (3 nodes). -/
def ordS11R173_Law4289 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4289. -/
theorem noS11R173_Law4289 : ∀ v : Magma.tup11R173,
    ¬ @Equation4289 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4289) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4289) (by native_decide) v.1 v.2
    ((@Law4289.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (3 nodes). -/
def ordS11R173_Law4291 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4291. -/
theorem noS11R173_Law4291 : ∀ v : Magma.tup11R173,
    ¬ @Equation4291 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4296 takes them (3 nodes). -/
def ordS11R173_Law4296 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4296. -/
theorem noS11R173_Law4296 : ∀ v : Magma.tup11R173,
    ¬ @Equation4296 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4296) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4296) (by native_decide) v.1 v.2
    ((@Law4296.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4300 takes them (3 nodes). -/
def ordS11R173_Law4300 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4300. -/
theorem noS11R173_Law4300 : ∀ v : Magma.tup11R173,
    ¬ @Equation4300 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4300) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4300) (by native_decide) v.1 v.2
    ((@Law4300.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4304 takes them (3 nodes). -/
def ordS11R173_Law4304 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4304. -/
theorem noS11R173_Law4304 : ∀ v : Magma.tup11R173,
    ¬ @Equation4304 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4304) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4304) (by native_decide) v.1 v.2
    ((@Law4304.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4310 takes them (3 nodes). -/
def ordS11R173_Law4310 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4310. -/
theorem noS11R173_Law4310 : ∀ v : Magma.tup11R173,
    ¬ @Equation4310 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4310) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4310) (by native_decide) v.1 v.2
    ((@Law4310.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4314 takes them (3 nodes). -/
def ordS11R173_Law4314 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4314. -/
theorem noS11R173_Law4314 : ∀ v : Magma.tup11R173,
    ¬ @Equation4314 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4315 takes them (3 nodes). -/
def ordS11R173_Law4315 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4315. -/
theorem noS11R173_Law4315 : ∀ v : Magma.tup11R173,
    ¬ @Equation4315 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4315) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4315) (by native_decide) v.1 v.2
    ((@Law4315.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4316 takes them (4 nodes). -/
def ordS11R173_Law4316 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4316. -/
theorem noS11R173_Law4316 : ∀ v : Magma.tup11R173,
    ¬ @Equation4316 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4316) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4316) (by native_decide) v.1 v.2
    ((@Law4316.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4317 takes them (3 nodes). -/
def ordS11R173_Law4317 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4317. -/
theorem noS11R173_Law4317 : ∀ v : Magma.tup11R173,
    ¬ @Equation4317 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4317) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4317) (by native_decide) v.1 v.2
    ((@Law4317.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4318 takes them (3 nodes). -/
def ordS11R173_Law4318 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4318. -/
theorem noS11R173_Law4318 : ∀ v : Magma.tup11R173,
    ¬ @Equation4318 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4318) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4318) (by native_decide) v.1 v.2
    ((@Law4318.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4319 takes them (3 nodes). -/
def ordS11R173_Law4319 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4319. -/
theorem noS11R173_Law4319 : ∀ v : Magma.tup11R173,
    ¬ @Equation4319 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4319) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4319) (by native_decide) v.1 v.2
    ((@Law4319.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4320 takes them (3 nodes). -/
def ordS11R173_Law4320 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4320. -/
theorem noS11R173_Law4320 : ∀ v : Magma.tup11R173,
    ¬ @Equation4320 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4320) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4320) (by native_decide) v.1 v.2
    ((@Law4320.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4323 takes them (3 nodes). -/
def ordS11R173_Law4323 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4323. -/
theorem noS11R173_Law4323 : ∀ v : Magma.tup11R173,
    ¬ @Equation4323 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4323) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4323) (by native_decide) v.1 v.2
    ((@Law4323.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4327 takes them (3 nodes). -/
def ordS11R173_Law4327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4327. -/
theorem noS11R173_Law4327 : ∀ v : Magma.tup11R173,
    ¬ @Equation4327 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4327) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4327) (by native_decide) v.1 v.2
    ((@Law4327.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4330 takes them (3 nodes). -/
def ordS11R173_Law4330 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4330. -/
theorem noS11R173_Law4330 : ∀ v : Magma.tup11R173,
    ¬ @Equation4330 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4330) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4330) (by native_decide) v.1 v.2
    ((@Law4330.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4334 takes them (3 nodes). -/
def ordS11R173_Law4334 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4334. -/
theorem noS11R173_Law4334 : ∀ v : Magma.tup11R173,
    ¬ @Equation4334 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4334) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4334) (by native_decide) v.1 v.2
    ((@Law4334.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4339 takes them (3 nodes). -/
def ordS11R173_Law4339 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4339. -/
theorem noS11R173_Law4339 : ∀ v : Magma.tup11R173,
    ¬ @Equation4339 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4339) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4339) (by native_decide) v.1 v.2
    ((@Law4339.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4340 takes them (4 nodes). -/
def ordS11R173_Law4340 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4340. -/
theorem noS11R173_Law4340 : ∀ v : Magma.tup11R173,
    ¬ @Equation4340 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4340) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4340) (by native_decide) v.1 v.2
    ((@Law4340.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4341 takes them (3 nodes). -/
def ordS11R173_Law4341 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4341. -/
theorem noS11R173_Law4341 : ∀ v : Magma.tup11R173,
    ¬ @Equation4341 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4341) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4341) (by native_decide) v.1 v.2
    ((@Law4341.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4342 takes them (3 nodes). -/
def ordS11R173_Law4342 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4342. -/
theorem noS11R173_Law4342 : ∀ v : Magma.tup11R173,
    ¬ @Equation4342 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4342) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4342) (by native_decide) v.1 v.2
    ((@Law4342.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4348 takes them (3 nodes). -/
def ordS11R173_Law4348 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4348. -/
theorem noS11R173_Law4348 : ∀ v : Magma.tup11R173,
    ¬ @Equation4348 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4348) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4348) (by native_decide) v.1 v.2
    ((@Law4348.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4351 takes them (3 nodes). -/
def ordS11R173_Law4351 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4351. -/
theorem noS11R173_Law4351 : ∀ v : Magma.tup11R173,
    ¬ @Equation4351 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4351) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4351) (by native_decide) v.1 v.2
    ((@Law4351.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4354 takes them (3 nodes). -/
def ordS11R173_Law4354 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4354. -/
theorem noS11R173_Law4354 : ∀ v : Magma.tup11R173,
    ¬ @Equation4354 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4354) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4354) (by native_decide) v.1 v.2
    ((@Law4354.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4357 takes them (3 nodes). -/
def ordS11R173_Law4357 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4357. -/
theorem noS11R173_Law4357 : ∀ v : Magma.tup11R173,
    ¬ @Equation4357 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4357) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4357) (by native_decide) v.1 v.2
    ((@Law4357.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4359 takes them (3 nodes). -/
def ordS11R173_Law4359 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4359. -/
theorem noS11R173_Law4359 : ∀ v : Magma.tup11R173,
    ¬ @Equation4359 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4359) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4359) (by native_decide) v.1 v.2
    ((@Law4359.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4360 takes them (4 nodes). -/
def ordS11R173_Law4360 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4360. -/
theorem noS11R173_Law4360 : ∀ v : Magma.tup11R173,
    ¬ @Equation4360 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4360) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4360) (by native_decide) v.1 v.2
    ((@Law4360.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (3 nodes). -/
def ordS11R173_Law4362 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4362. -/
theorem noS11R173_Law4362 : ∀ v : Magma.tup11R173,
    ¬ @Equation4362 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4367 takes them (3 nodes). -/
def ordS11R173_Law4367 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4367. -/
theorem noS11R173_Law4367 : ∀ v : Magma.tup11R173,
    ¬ @Equation4367 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4367) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4367) (by native_decide) v.1 v.2
    ((@Law4367.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4374 takes them (3 nodes). -/
def ordS11R173_Law4374 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4374. -/
theorem noS11R173_Law4374 : ∀ v : Magma.tup11R173,
    ¬ @Equation4374 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4374) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4374) (by native_decide) v.1 v.2
    ((@Law4374.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4382 takes them (4 nodes). -/
def ordS11R173_Law4382 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4382. -/
theorem noS11R173_Law4382 : ∀ v : Magma.tup11R173,
    ¬ @Equation4382 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4382) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4382) (by native_decide) v.1 v.2
    ((@Law4382.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4385 takes them (3 nodes). -/
def ordS11R173_Law4385 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4385. -/
theorem noS11R173_Law4385 : ∀ v : Magma.tup11R173,
    ¬ @Equation4385 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4385) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4385) (by native_decide) v.1 v.2
    ((@Law4385.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4395 takes them (3 nodes). -/
def ordS11R173_Law4395 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4395. -/
theorem noS11R173_Law4395 : ∀ v : Magma.tup11R173,
    ¬ @Equation4395 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4395) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4395) (by native_decide) v.1 v.2
    ((@Law4395.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4396 takes them (4 nodes). -/
def ordS11R173_Law4396 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4396. -/
theorem noS11R173_Law4396 : ∀ v : Magma.tup11R173,
    ¬ @Equation4396 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4396) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4396) (by native_decide) v.1 v.2
    ((@Law4396.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4399 takes them (4 nodes). -/
def ordS11R173_Law4399 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4399. -/
theorem noS11R173_Law4399 : ∀ v : Magma.tup11R173,
    ¬ @Equation4399 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4399) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4399) (by native_decide) v.1 v.2
    ((@Law4399.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4401 takes them (3 nodes). -/
def ordS11R173_Law4401 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4401. -/
theorem noS11R173_Law4401 : ∀ v : Magma.tup11R173,
    ¬ @Equation4401 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4401) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4401) (by native_decide) v.1 v.2
    ((@Law4401.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4406 takes them (3 nodes). -/
def ordS11R173_Law4406 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4406. -/
theorem noS11R173_Law4406 : ∀ v : Magma.tup11R173,
    ¬ @Equation4406 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4406) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4406) (by native_decide) v.1 v.2
    ((@Law4406.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4432 takes them (4 nodes). -/
def ordS11R173_Law4432 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4432. -/
theorem noS11R173_Law4432 : ∀ v : Magma.tup11R173,
    ¬ @Equation4432 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4432) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4432) (by native_decide) v.1 v.2
    ((@Law4432.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4433 takes them (3 nodes). -/
def ordS11R173_Law4433 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4433. -/
theorem noS11R173_Law4433 : ∀ v : Magma.tup11R173,
    ¬ @Equation4433 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4433) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4433) (by native_decide) v.1 v.2
    ((@Law4433.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4436 takes them (3 nodes). -/
def ordS11R173_Law4436 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4436. -/
theorem noS11R173_Law4436 : ∀ v : Magma.tup11R173,
    ¬ @Equation4436 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4436) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4436) (by native_decide) v.1 v.2
    ((@Law4436.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4445 takes them (3 nodes). -/
def ordS11R173_Law4445 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4445. -/
theorem noS11R173_Law4445 : ∀ v : Magma.tup11R173,
    ¬ @Equation4445 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4445) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4445) (by native_decide) v.1 v.2
    ((@Law4445.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4452 takes them (3 nodes). -/
def ordS11R173_Law4452 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4452. -/
theorem noS11R173_Law4452 : ∀ v : Magma.tup11R173,
    ¬ @Equation4452 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4452) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4452) (by native_decide) v.1 v.2
    ((@Law4452.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4472 takes them (3 nodes). -/
def ordS11R173_Law4472 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4472. -/
theorem noS11R173_Law4472 : ∀ v : Magma.tup11R173,
    ¬ @Equation4472 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4472) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4472) (by native_decide) v.1 v.2
    ((@Law4472.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4473 takes them (4 nodes). -/
def ordS11R173_Law4473 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4473. -/
theorem noS11R173_Law4473 : ∀ v : Magma.tup11R173,
    ¬ @Equation4473 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4473) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4473) (by native_decide) v.1 v.2
    ((@Law4473.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4480 takes them (3 nodes). -/
def ordS11R173_Law4480 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4480. -/
theorem noS11R173_Law4480 : ∀ v : Magma.tup11R173,
    ¬ @Equation4480 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4480) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4480) (by native_decide) v.1 v.2
    ((@Law4480.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4583 takes them (3 nodes). -/
def ordS11R173_Law4583 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4583. -/
theorem noS11R173_Law4583 : ∀ v : Magma.tup11R173,
    ¬ @Equation4583 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4583) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4583) (by native_decide) v.1 v.2
    ((@Law4583.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4584 takes them (4 nodes). -/
def ordS11R173_Law4584 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4584. -/
theorem noS11R173_Law4584 : ∀ v : Magma.tup11R173,
    ¬ @Equation4584 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4584) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4584) (by native_decide) v.1 v.2
    ((@Law4584.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4586 takes them (3 nodes). -/
def ordS11R173_Law4586 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4586. -/
theorem noS11R173_Law4586 : ∀ v : Magma.tup11R173,
    ¬ @Equation4586 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4586) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4586) (by native_decide) v.1 v.2
    ((@Law4586.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4587 takes them (3 nodes). -/
def ordS11R173_Law4587 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4587. -/
theorem noS11R173_Law4587 : ∀ v : Magma.tup11R173,
    ¬ @Equation4587 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4587) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4587) (by native_decide) v.1 v.2
    ((@Law4587.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4590 takes them (3 nodes). -/
def ordS11R173_Law4590 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4590. -/
theorem noS11R173_Law4590 : ∀ v : Magma.tup11R173,
    ¬ @Equation4590 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4590) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4590) (by native_decide) v.1 v.2
    ((@Law4590.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4593 takes them (3 nodes). -/
def ordS11R173_Law4593 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4593. -/
theorem noS11R173_Law4593 : ∀ v : Magma.tup11R173,
    ¬ @Equation4593 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4593) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4593) (by native_decide) v.1 v.2
    ((@Law4593.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4597 takes them (3 nodes). -/
def ordS11R173_Law4597 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4597. -/
theorem noS11R173_Law4597 : ∀ v : Magma.tup11R173,
    ¬ @Equation4597 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4597) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4597) (by native_decide) v.1 v.2
    ((@Law4597.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4598 takes them (3 nodes). -/
def ordS11R173_Law4598 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4598. -/
theorem noS11R173_Law4598 : ∀ v : Magma.tup11R173,
    ¬ @Equation4598 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4598) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4598) (by native_decide) v.1 v.2
    ((@Law4598.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4599 takes them (4 nodes). -/
def ordS11R173_Law4599 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4599. -/
theorem noS11R173_Law4599 : ∀ v : Magma.tup11R173,
    ¬ @Equation4599 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4599) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4599) (by native_decide) v.1 v.2
    ((@Law4599.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch11R173_refutes_7 :
    FamilyRefutes Magma.srch11R173 [
      4155, 4158, 4161, 4165, 4168, 4171, 4175, 4179, 4183, 4187, 4192, 4196, 4200, 4204, 4209,
      4213, 4217, 4221, 4226, 4230, 4234, 4238, 4243, 4248, 4253, 4258, 4268, 4269, 4270, 4271,
      4272, 4278, 4282, 4284, 4285, 4286, 4287, 4288, 4289, 4291, 4296, 4300, 4304, 4310, 4314,
      4315, 4316, 4317, 4318, 4319, 4320, 4323, 4327, 4330, 4334, 4339, 4340, 4341, 4342, 4348,
      4351, 4354, 4357, 4359, 4360, 4362, 4367, 4374, 4382, 4385, 4395, 4396, 4399, 4401, 4406,
      4432, 4433, 4436, 4445, 4452, 4472, 4473, 4480, 4583, 4584, 4586, 4587, 4590, 4593, 4597,
      4598, 4599
    ] :=
  ⟨noS11R173_Law4155, noS11R173_Law4158, noS11R173_Law4161, noS11R173_Law4165, noS11R173_Law4168, noS11R173_Law4171, noS11R173_Law4175, noS11R173_Law4179, noS11R173_Law4183, noS11R173_Law4187, noS11R173_Law4192, noS11R173_Law4196, noS11R173_Law4200, noS11R173_Law4204, noS11R173_Law4209, noS11R173_Law4213, noS11R173_Law4217, noS11R173_Law4221, noS11R173_Law4226, noS11R173_Law4230, noS11R173_Law4234, noS11R173_Law4238, noS11R173_Law4243, noS11R173_Law4248, noS11R173_Law4253, noS11R173_Law4258, noS11R173_Law4268, noS11R173_Law4269, noS11R173_Law4270, noS11R173_Law4271, noS11R173_Law4272, noS11R173_Law4278, noS11R173_Law4282, noS11R173_Law4284, noS11R173_Law4285, noS11R173_Law4286, noS11R173_Law4287, noS11R173_Law4288, noS11R173_Law4289, noS11R173_Law4291, noS11R173_Law4296, noS11R173_Law4300, noS11R173_Law4304, noS11R173_Law4310, noS11R173_Law4314, noS11R173_Law4315, noS11R173_Law4316, noS11R173_Law4317, noS11R173_Law4318, noS11R173_Law4319, noS11R173_Law4320, noS11R173_Law4323, noS11R173_Law4327, noS11R173_Law4330, noS11R173_Law4334, noS11R173_Law4339, noS11R173_Law4340, noS11R173_Law4341, noS11R173_Law4342, noS11R173_Law4348, noS11R173_Law4351, noS11R173_Law4354, noS11R173_Law4357, noS11R173_Law4359, noS11R173_Law4360, noS11R173_Law4362, noS11R173_Law4367, noS11R173_Law4374, noS11R173_Law4382, noS11R173_Law4385, noS11R173_Law4395, noS11R173_Law4396, noS11R173_Law4399, noS11R173_Law4401, noS11R173_Law4406, noS11R173_Law4432, noS11R173_Law4433, noS11R173_Law4436, noS11R173_Law4445, noS11R173_Law4452, noS11R173_Law4472, noS11R173_Law4473, noS11R173_Law4480, noS11R173_Law4583, noS11R173_Law4584, noS11R173_Law4586, noS11R173_Law4587, noS11R173_Law4590, noS11R173_Law4593, noS11R173_Law4597, noS11R173_Law4598, noS11R173_Law4599⟩
