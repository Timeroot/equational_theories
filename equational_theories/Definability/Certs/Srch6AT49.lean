import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 50 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `34`
equations here, 2,613 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4188 takes them (35 nodes). -/
def ordS6A_Law4188 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4188. -/
theorem noS6A_Law4188 : ∀ v : Magma.tupS6A,
    ¬ @Equation4188 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4188) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4188) (by native_decide) v.1 v.2
    ((@Law4188.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4189 takes them (37 nodes). -/
def ordS6A_Law4189 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4189. -/
theorem noS6A_Law4189 : ∀ v : Magma.tupS6A,
    ¬ @Equation4189 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4189) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4189) (by native_decide) v.1 v.2
    ((@Law4189.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4190 takes them (30 nodes). -/
def ordS6A_Law4190 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4190. -/
theorem noS6A_Law4190 : ∀ v : Magma.tupS6A,
    ¬ @Equation4190 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4190) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4190) (by native_decide) v.1 v.2
    ((@Law4190.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4191 takes them (69 nodes). -/
def ordS6A_Law4191 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4191. -/
theorem noS6A_Law4191 : ∀ v : Magma.tupS6A,
    ¬ @Equation4191 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4191) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4191) (by native_decide) v.1 v.2
    ((@Law4191.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4193 takes them (70 nodes). -/
def ordS6A_Law4193 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4193. -/
theorem noS6A_Law4193 : ∀ v : Magma.tupS6A,
    ¬ @Equation4193 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4193) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4193) (by native_decide) v.1 v.2
    ((@Law4193.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4194 takes them (69 nodes). -/
def ordS6A_Law4194 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4194. -/
theorem noS6A_Law4194 : ∀ v : Magma.tupS6A,
    ¬ @Equation4194 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4194) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4194) (by native_decide) v.1 v.2
    ((@Law4194.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4195 takes them (120 nodes). -/
def ordS6A_Law4195 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4195. -/
theorem noS6A_Law4195 : ∀ v : Magma.tupS6A,
    ¬ @Equation4195 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4195) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4195) (by native_decide) v.1 v.2
    ((@Law4195.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4196 takes them (256 nodes). -/
def ordS6A_Law4196 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4196. -/
theorem noS6A_Law4196 : ∀ v : Magma.tupS6A,
    ¬ @Equation4196 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4196) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4196) (by native_decide) v.1 v.2
    ((@Law4196.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4197 takes them (158 nodes). -/
def ordS6A_Law4197 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4197. -/
theorem noS6A_Law4197 : ∀ v : Magma.tupS6A,
    ¬ @Equation4197 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4197) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4197) (by native_decide) v.1 v.2
    ((@Law4197.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4198 takes them (71 nodes). -/
def ordS6A_Law4198 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4198. -/
theorem noS6A_Law4198 : ∀ v : Magma.tupS6A,
    ¬ @Equation4198 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4198) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4198) (by native_decide) v.1 v.2
    ((@Law4198.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4199 takes them (69 nodes). -/
def ordS6A_Law4199 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4199. -/
theorem noS6A_Law4199 : ∀ v : Magma.tupS6A,
    ¬ @Equation4199 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4199) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4199) (by native_decide) v.1 v.2
    ((@Law4199.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4201 takes them (69 nodes). -/
def ordS6A_Law4201 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4201. -/
theorem noS6A_Law4201 : ∀ v : Magma.tupS6A,
    ¬ @Equation4201 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4201) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4201) (by native_decide) v.1 v.2
    ((@Law4201.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4202 takes them (69 nodes). -/
def ordS6A_Law4202 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4202. -/
theorem noS6A_Law4202 : ∀ v : Magma.tupS6A,
    ¬ @Equation4202 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4202) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4202) (by native_decide) v.1 v.2
    ((@Law4202.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4203 takes them (55 nodes). -/
def ordS6A_Law4203 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4203. -/
theorem noS6A_Law4203 : ∀ v : Magma.tupS6A,
    ¬ @Equation4203 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4203) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4203) (by native_decide) v.1 v.2
    ((@Law4203.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4204 takes them (137 nodes). -/
def ordS6A_Law4204 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4204. -/
theorem noS6A_Law4204 : ∀ v : Magma.tupS6A,
    ¬ @Equation4204 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4204) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4204) (by native_decide) v.1 v.2
    ((@Law4204.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4205 takes them (55 nodes). -/
def ordS6A_Law4205 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4205. -/
theorem noS6A_Law4205 : ∀ v : Magma.tupS6A,
    ¬ @Equation4205 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4205) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4205) (by native_decide) v.1 v.2
    ((@Law4205.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4206 takes them (55 nodes). -/
def ordS6A_Law4206 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4206. -/
theorem noS6A_Law4206 : ∀ v : Magma.tupS6A,
    ¬ @Equation4206 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4206) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4206) (by native_decide) v.1 v.2
    ((@Law4206.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4207 takes them (55 nodes). -/
def ordS6A_Law4207 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4207. -/
theorem noS6A_Law4207 : ∀ v : Magma.tupS6A,
    ¬ @Equation4207 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4207) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4207) (by native_decide) v.1 v.2
    ((@Law4207.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4208 takes them (100 nodes). -/
def ordS6A_Law4208 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4208. -/
theorem noS6A_Law4208 : ∀ v : Magma.tupS6A,
    ¬ @Equation4208 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4208) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4208) (by native_decide) v.1 v.2
    ((@Law4208.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4210 takes them (171 nodes). -/
def ordS6A_Law4210 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4210. -/
theorem noS6A_Law4210 : ∀ v : Magma.tupS6A,
    ¬ @Equation4210 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4210) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4210) (by native_decide) v.1 v.2
    ((@Law4210.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4211 takes them (59 nodes). -/
def ordS6A_Law4211 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4211. -/
theorem noS6A_Law4211 : ∀ v : Magma.tupS6A,
    ¬ @Equation4211 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4211) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4211) (by native_decide) v.1 v.2
    ((@Law4211.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4212 takes them (43 nodes). -/
def ordS6A_Law4212 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4212. -/
theorem noS6A_Law4212 : ∀ v : Magma.tupS6A,
    ¬ @Equation4212 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4212) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4212) (by native_decide) v.1 v.2
    ((@Law4212.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4213 takes them (103 nodes). -/
def ordS6A_Law4213 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4213. -/
theorem noS6A_Law4213 : ∀ v : Magma.tupS6A,
    ¬ @Equation4213 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4213) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4213) (by native_decide) v.1 v.2
    ((@Law4213.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4214 takes them (38 nodes). -/
def ordS6A_Law4214 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4214. -/
theorem noS6A_Law4214 : ∀ v : Magma.tupS6A,
    ¬ @Equation4214 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4214) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4214) (by native_decide) v.1 v.2
    ((@Law4214.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4215 takes them (31 nodes). -/
def ordS6A_Law4215 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4215. -/
theorem noS6A_Law4215 : ∀ v : Magma.tupS6A,
    ¬ @Equation4215 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4215) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4215) (by native_decide) v.1 v.2
    ((@Law4215.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4216 takes them (133 nodes). -/
def ordS6A_Law4216 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4216. -/
theorem noS6A_Law4216 : ∀ v : Magma.tupS6A,
    ¬ @Equation4216 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4216) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4216) (by native_decide) v.1 v.2
    ((@Law4216.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4217 takes them (120 nodes). -/
def ordS6A_Law4217 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4217. -/
theorem noS6A_Law4217 : ∀ v : Magma.tupS6A,
    ¬ @Equation4217 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4217) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4217) (by native_decide) v.1 v.2
    ((@Law4217.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4218 takes them (73 nodes). -/
def ordS6A_Law4218 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4218. -/
theorem noS6A_Law4218 : ∀ v : Magma.tupS6A,
    ¬ @Equation4218 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4218) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4218) (by native_decide) v.1 v.2
    ((@Law4218.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4219 takes them (68 nodes). -/
def ordS6A_Law4219 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4219. -/
theorem noS6A_Law4219 : ∀ v : Magma.tupS6A,
    ¬ @Equation4219 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4219) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4219) (by native_decide) v.1 v.2
    ((@Law4219.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4220 takes them (37 nodes). -/
def ordS6A_Law4220 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4220. -/
theorem noS6A_Law4220 : ∀ v : Magma.tupS6A,
    ¬ @Equation4220 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4220) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4220) (by native_decide) v.1 v.2
    ((@Law4220.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4221 takes them (67 nodes). -/
def ordS6A_Law4221 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4221. -/
theorem noS6A_Law4221 : ∀ v : Magma.tupS6A,
    ¬ @Equation4221 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4221) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4221) (by native_decide) v.1 v.2
    ((@Law4221.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4222 takes them (32 nodes). -/
def ordS6A_Law4222 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4222. -/
theorem noS6A_Law4222 : ∀ v : Magma.tupS6A,
    ¬ @Equation4222 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4222) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4222) (by native_decide) v.1 v.2
    ((@Law4222.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4223 takes them (32 nodes). -/
def ordS6A_Law4223 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4223. -/
theorem noS6A_Law4223 : ∀ v : Magma.tupS6A,
    ¬ @Equation4223 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4223) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4223) (by native_decide) v.1 v.2
    ((@Law4223.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4224 takes them (27 nodes). -/
def ordS6A_Law4224 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4224. -/
theorem noS6A_Law4224 : ∀ v : Magma.tupS6A,
    ¬ @Equation4224 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4224) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4224) (by native_decide) v.1 v.2
    ((@Law4224.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `34` equations. -/
theorem srch6A_refutes_49 :
    FamilyRefutes Magma.srch6A [
      4188, 4189, 4190, 4191, 4193, 4194, 4195, 4196, 4197, 4198, 4199, 4201, 4202, 4203, 4204,
      4205, 4206, 4207, 4208, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220,
      4221, 4222, 4223, 4224
    ] :=
  ⟨noS6A_Law4188, noS6A_Law4189, noS6A_Law4190, noS6A_Law4191, noS6A_Law4193, noS6A_Law4194, noS6A_Law4195, noS6A_Law4196, noS6A_Law4197, noS6A_Law4198, noS6A_Law4199, noS6A_Law4201, noS6A_Law4202, noS6A_Law4203, noS6A_Law4204, noS6A_Law4205, noS6A_Law4206, noS6A_Law4207, noS6A_Law4208, noS6A_Law4210, noS6A_Law4211, noS6A_Law4212, noS6A_Law4213, noS6A_Law4214, noS6A_Law4215, noS6A_Law4216, noS6A_Law4217, noS6A_Law4218, noS6A_Law4219, noS6A_Law4220, noS6A_Law4221, noS6A_Law4222, noS6A_Law4223, noS6A_Law4224⟩
