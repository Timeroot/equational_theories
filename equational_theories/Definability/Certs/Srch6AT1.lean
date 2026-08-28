import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 2 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `22`
equations here, 3,101 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 154 takes them (515 nodes). -/
def ordS6A_Law154 : List (Fin 11) := [8, 6, 5, 10, 9, 1, 7, 2, 4, 0, 3]

/-- No member of the class satisfies equation 154. -/
theorem noS6A_Law154 : ∀ v : Magma.tupS6A,
    ¬ @Equation154 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law154) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law154) (by native_decide) v.1 v.2
    ((@Law154.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 155 takes them (172 nodes). -/
def ordS6A_Law155 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 155. -/
theorem noS6A_Law155 : ∀ v : Magma.tupS6A,
    ¬ @Equation155 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law155) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law155) (by native_decide) v.1 v.2
    ((@Law155.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 157 takes them (310 nodes). -/
def ordS6A_Law157 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 157. -/
theorem noS6A_Law157 : ∀ v : Magma.tupS6A,
    ¬ @Equation157 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law157) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law157) (by native_decide) v.1 v.2
    ((@Law157.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 158 takes them (58 nodes). -/
def ordS6A_Law158 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 158. -/
theorem noS6A_Law158 : ∀ v : Magma.tupS6A,
    ¬ @Equation158 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law158) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law158) (by native_decide) v.1 v.2
    ((@Law158.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 162 takes them (169 nodes). -/
def ordS6A_Law162 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 162. -/
theorem noS6A_Law162 : ∀ v : Magma.tupS6A,
    ¬ @Equation162 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law162) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law162) (by native_decide) v.1 v.2
    ((@Law162.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 163 takes them (65 nodes). -/
def ordS6A_Law163 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 163. -/
theorem noS6A_Law163 : ∀ v : Magma.tupS6A,
    ¬ @Equation163 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law163) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law163) (by native_decide) v.1 v.2
    ((@Law163.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 164 takes them (106 nodes). -/
def ordS6A_Law164 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 164. -/
theorem noS6A_Law164 : ∀ v : Magma.tupS6A,
    ¬ @Equation164 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law164) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law164) (by native_decide) v.1 v.2
    ((@Law164.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 165 takes them (40 nodes). -/
def ordS6A_Law165 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 165. -/
theorem noS6A_Law165 : ∀ v : Magma.tupS6A,
    ¬ @Equation165 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law165) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law165) (by native_decide) v.1 v.2
    ((@Law165.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 169 takes them (254 nodes). -/
def ordS6A_Law169 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 169. -/
theorem noS6A_Law169 : ∀ v : Magma.tupS6A,
    ¬ @Equation169 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law169) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law169) (by native_decide) v.1 v.2
    ((@Law169.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 172 takes them (61 nodes). -/
def ordS6A_Law172 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 172. -/
theorem noS6A_Law172 : ∀ v : Magma.tupS6A,
    ¬ @Equation172 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law172) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law172) (by native_decide) v.1 v.2
    ((@Law172.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 176 takes them (448 nodes). -/
def ordS6A_Law176 : List (Fin 11) := [1, 6, 5, 4, 0, 3, 2, 10, 7, 9, 8]

/-- No member of the class satisfies equation 176. -/
theorem noS6A_Law176 : ∀ v : Magma.tupS6A,
    ¬ @Equation176 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law176) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law176) (by native_decide) v.1 v.2
    ((@Law176.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 182 takes them (137 nodes). -/
def ordS6A_Law182 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 182. -/
theorem noS6A_Law182 : ∀ v : Magma.tupS6A,
    ¬ @Equation182 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law182) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law182) (by native_decide) v.1 v.2
    ((@Law182.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 186 takes them (141 nodes). -/
def ordS6A_Law186 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 186. -/
theorem noS6A_Law186 : ∀ v : Magma.tupS6A,
    ¬ @Equation186 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law186) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law186) (by native_decide) v.1 v.2
    ((@Law186.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 190 takes them (48 nodes). -/
def ordS6A_Law190 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 190. -/
theorem noS6A_Law190 : ∀ v : Magma.tupS6A,
    ¬ @Equation190 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law190) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law190) (by native_decide) v.1 v.2
    ((@Law190.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 198 takes them (43 nodes). -/
def ordS6A_Law198 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 198. -/
theorem noS6A_Law198 : ∀ v : Magma.tupS6A,
    ¬ @Equation198 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law198) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law198) (by native_decide) v.1 v.2
    ((@Law198.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 204 takes them (98 nodes). -/
def ordS6A_Law204 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 204. -/
theorem noS6A_Law204 : ∀ v : Magma.tupS6A,
    ¬ @Equation204 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law204) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law204) (by native_decide) v.1 v.2
    ((@Law204.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 206 takes them (194 nodes). -/
def ordS6A_Law206 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 206. -/
theorem noS6A_Law206 : ∀ v : Magma.tupS6A,
    ¬ @Equation206 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law206) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law206) (by native_decide) v.1 v.2
    ((@Law206.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 207 takes them (41 nodes). -/
def ordS6A_Law207 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 207. -/
theorem noS6A_Law207 : ∀ v : Magma.tupS6A,
    ¬ @Equation207 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law207) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law207) (by native_decide) v.1 v.2
    ((@Law207.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 210 takes them (40 nodes). -/
def ordS6A_Law210 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 210. -/
theorem noS6A_Law210 : ∀ v : Magma.tupS6A,
    ¬ @Equation210 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law210) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law210) (by native_decide) v.1 v.2
    ((@Law210.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 213 takes them (60 nodes). -/
def ordS6A_Law213 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 213. -/
theorem noS6A_Law213 : ∀ v : Magma.tupS6A,
    ¬ @Equation213 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law213) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law213) (by native_decide) v.1 v.2
    ((@Law213.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 216 takes them (68 nodes). -/
def ordS6A_Law216 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 216. -/
theorem noS6A_Law216 : ∀ v : Magma.tupS6A,
    ¬ @Equation216 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law216) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law216) (by native_decide) v.1 v.2
    ((@Law216.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 217 takes them (33 nodes). -/
def ordS6A_Law217 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 217. -/
theorem noS6A_Law217 : ∀ v : Magma.tupS6A,
    ¬ @Equation217 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law217) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law217) (by native_decide) v.1 v.2
    ((@Law217.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `22` equations. -/
theorem srch6A_refutes_1 :
    FamilyRefutes Magma.srch6A [
      154, 155, 157, 158, 162, 163, 164, 165, 169, 172, 176, 182, 186, 190, 198, 204, 206, 207,
      210, 213, 216, 217
    ] :=
  ⟨noS6A_Law154, noS6A_Law155, noS6A_Law157, noS6A_Law158, noS6A_Law162, noS6A_Law163, noS6A_Law164, noS6A_Law165, noS6A_Law169, noS6A_Law172, noS6A_Law176, noS6A_Law182, noS6A_Law186, noS6A_Law190, noS6A_Law198, noS6A_Law204, noS6A_Law206, noS6A_Law207, noS6A_Law210, noS6A_Law213, noS6A_Law216, noS6A_Law217⟩
