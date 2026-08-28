import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 49 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `21`
equations here, 3,144 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4164 takes them (445 nodes). -/
def ordS6A_Law4164 : List (Fin 11) := [9, 10, 0, 1, 8, 6, 4, 2, 5, 3, 7]

/-- No member of the class satisfies equation 4164. -/
theorem noS6A_Law4164 : ∀ v : Magma.tupS6A,
    ¬ @Equation4164 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4164) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law4164) (by native_decide) v.1 v.2
    ((@Law4164.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4166 takes them (130 nodes). -/
def ordS6A_Law4166 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4166. -/
theorem noS6A_Law4166 : ∀ v : Magma.tupS6A,
    ¬ @Equation4166 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4166) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4166) (by native_decide) v.1 v.2
    ((@Law4166.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4168 takes them (307 nodes). -/
def ordS6A_Law4168 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4168. -/
theorem noS6A_Law4168 : ∀ v : Magma.tupS6A,
    ¬ @Equation4168 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4168) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law4168) (by native_decide) v.1 v.2
    ((@Law4168.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4169 takes them (134 nodes). -/
def ordS6A_Law4169 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4169. -/
theorem noS6A_Law4169 : ∀ v : Magma.tupS6A,
    ¬ @Equation4169 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4169) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4169) (by native_decide) v.1 v.2
    ((@Law4169.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4170 takes them (151 nodes). -/
def ordS6A_Law4170 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4170. -/
theorem noS6A_Law4170 : ∀ v : Magma.tupS6A,
    ¬ @Equation4170 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4170) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4170) (by native_decide) v.1 v.2
    ((@Law4170.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4171 takes them (261 nodes). -/
def ordS6A_Law4171 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4171. -/
theorem noS6A_Law4171 : ∀ v : Magma.tupS6A,
    ¬ @Equation4171 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4171) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4171) (by native_decide) v.1 v.2
    ((@Law4171.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4172 takes them (165 nodes). -/
def ordS6A_Law4172 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4172. -/
theorem noS6A_Law4172 : ∀ v : Magma.tupS6A,
    ¬ @Equation4172 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4172) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4172) (by native_decide) v.1 v.2
    ((@Law4172.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4173 takes them (128 nodes). -/
def ordS6A_Law4173 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4173. -/
theorem noS6A_Law4173 : ∀ v : Magma.tupS6A,
    ¬ @Equation4173 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4173) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4173) (by native_decide) v.1 v.2
    ((@Law4173.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4174 takes them (119 nodes). -/
def ordS6A_Law4174 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4174. -/
theorem noS6A_Law4174 : ∀ v : Magma.tupS6A,
    ¬ @Equation4174 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4174) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4174) (by native_decide) v.1 v.2
    ((@Law4174.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4176 takes them (172 nodes). -/
def ordS6A_Law4176 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4176. -/
theorem noS6A_Law4176 : ∀ v : Magma.tupS6A,
    ¬ @Equation4176 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4176) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4176) (by native_decide) v.1 v.2
    ((@Law4176.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4177 takes them (70 nodes). -/
def ordS6A_Law4177 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4177. -/
theorem noS6A_Law4177 : ∀ v : Magma.tupS6A,
    ¬ @Equation4177 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4177) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4177) (by native_decide) v.1 v.2
    ((@Law4177.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4178 takes them (121 nodes). -/
def ordS6A_Law4178 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4178. -/
theorem noS6A_Law4178 : ∀ v : Magma.tupS6A,
    ¬ @Equation4178 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4178) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4178) (by native_decide) v.1 v.2
    ((@Law4178.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4179 takes them (201 nodes). -/
def ordS6A_Law4179 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4179. -/
theorem noS6A_Law4179 : ∀ v : Magma.tupS6A,
    ¬ @Equation4179 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4179) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4179) (by native_decide) v.1 v.2
    ((@Law4179.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4180 takes them (91 nodes). -/
def ordS6A_Law4180 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4180. -/
theorem noS6A_Law4180 : ∀ v : Magma.tupS6A,
    ¬ @Equation4180 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4180) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4180) (by native_decide) v.1 v.2
    ((@Law4180.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4181 takes them (86 nodes). -/
def ordS6A_Law4181 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4181. -/
theorem noS6A_Law4181 : ∀ v : Magma.tupS6A,
    ¬ @Equation4181 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4181) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4181) (by native_decide) v.1 v.2
    ((@Law4181.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4182 takes them (145 nodes). -/
def ordS6A_Law4182 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4182. -/
theorem noS6A_Law4182 : ∀ v : Magma.tupS6A,
    ¬ @Equation4182 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4182) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4182) (by native_decide) v.1 v.2
    ((@Law4182.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4183 takes them (137 nodes). -/
def ordS6A_Law4183 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4183. -/
theorem noS6A_Law4183 : ∀ v : Magma.tupS6A,
    ¬ @Equation4183 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4183) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4183) (by native_decide) v.1 v.2
    ((@Law4183.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4184 takes them (41 nodes). -/
def ordS6A_Law4184 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4184. -/
theorem noS6A_Law4184 : ∀ v : Magma.tupS6A,
    ¬ @Equation4184 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4184) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4184) (by native_decide) v.1 v.2
    ((@Law4184.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4185 takes them (34 nodes). -/
def ordS6A_Law4185 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4185. -/
theorem noS6A_Law4185 : ∀ v : Magma.tupS6A,
    ¬ @Equation4185 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4185) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4185) (by native_decide) v.1 v.2
    ((@Law4185.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4186 takes them (73 nodes). -/
def ordS6A_Law4186 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4186. -/
theorem noS6A_Law4186 : ∀ v : Magma.tupS6A,
    ¬ @Equation4186 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4186) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4186) (by native_decide) v.1 v.2
    ((@Law4186.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4187 takes them (133 nodes). -/
def ordS6A_Law4187 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4187. -/
theorem noS6A_Law4187 : ∀ v : Magma.tupS6A,
    ¬ @Equation4187 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4187) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4187) (by native_decide) v.1 v.2
    ((@Law4187.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `21` equations. -/
theorem srch6A_refutes_48 :
    FamilyRefutes Magma.srch6A [
      4164, 4166, 4168, 4169, 4170, 4171, 4172, 4173, 4174, 4176, 4177, 4178, 4179, 4180, 4181,
      4182, 4183, 4184, 4185, 4186, 4187
    ] :=
  ⟨noS6A_Law4164, noS6A_Law4166, noS6A_Law4168, noS6A_Law4169, noS6A_Law4170, noS6A_Law4171, noS6A_Law4172, noS6A_Law4173, noS6A_Law4174, noS6A_Law4176, noS6A_Law4177, noS6A_Law4178, noS6A_Law4179, noS6A_Law4180, noS6A_Law4181, noS6A_Law4182, noS6A_Law4183, noS6A_Law4184, noS6A_Law4185, noS6A_Law4186, noS6A_Law4187⟩
