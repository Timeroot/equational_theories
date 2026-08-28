import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 10 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `26`
equations here, 2,886 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1072 takes them (155 nodes). -/
def ordS6A_Law1072 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1072. -/
theorem noS6A_Law1072 : ∀ v : Magma.tupS6A,
    ¬ @Equation1072 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1072) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1072) (by native_decide) v.1 v.2
    ((@Law1072.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1078 takes them (78 nodes). -/
def ordS6A_Law1078 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1078. -/
theorem noS6A_Law1078 : ∀ v : Magma.tupS6A,
    ¬ @Equation1078 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1078) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1078) (by native_decide) v.1 v.2
    ((@Law1078.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1082 takes them (499 nodes). -/
def ordS6A_Law1082 : List (Fin 11) := [4, 5, 9, 1, 6, 10, 7, 8, 0, 2, 3]

/-- No member of the class satisfies equation 1082. -/
theorem noS6A_Law1082 : ∀ v : Magma.tupS6A,
    ¬ @Equation1082 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1082) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1082) (by native_decide) v.1 v.2
    ((@Law1082.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1088 takes them (92 nodes). -/
def ordS6A_Law1088 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1088. -/
theorem noS6A_Law1088 : ∀ v : Magma.tupS6A,
    ¬ @Equation1088 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1088) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1088) (by native_decide) v.1 v.2
    ((@Law1088.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1092 takes them (92 nodes). -/
def ordS6A_Law1092 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1092. -/
theorem noS6A_Law1092 : ∀ v : Magma.tupS6A,
    ¬ @Equation1092 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1092) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1092) (by native_decide) v.1 v.2
    ((@Law1092.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1096 takes them (143 nodes). -/
def ordS6A_Law1096 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1096. -/
theorem noS6A_Law1096 : ∀ v : Magma.tupS6A,
    ¬ @Equation1096 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1096) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1096) (by native_decide) v.1 v.2
    ((@Law1096.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1100 takes them (100 nodes). -/
def ordS6A_Law1100 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1100. -/
theorem noS6A_Law1100 : ∀ v : Magma.tupS6A,
    ¬ @Equation1100 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1100) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1100) (by native_decide) v.1 v.2
    ((@Law1100.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1104 takes them (73 nodes). -/
def ordS6A_Law1104 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1104. -/
theorem noS6A_Law1104 : ∀ v : Magma.tupS6A,
    ¬ @Equation1104 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1104) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1104) (by native_decide) v.1 v.2
    ((@Law1104.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1115 takes them (95 nodes). -/
def ordS6A_Law1115 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1115. -/
theorem noS6A_Law1115 : ∀ v : Magma.tupS6A,
    ¬ @Equation1115 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1115) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1115) (by native_decide) v.1 v.2
    ((@Law1115.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1119 takes them (302 nodes). -/
def ordS6A_Law1119 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1119. -/
theorem noS6A_Law1119 : ∀ v : Magma.tupS6A,
    ¬ @Equation1119 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1119) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1119) (by native_decide) v.1 v.2
    ((@Law1119.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1125 takes them (47 nodes). -/
def ordS6A_Law1125 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1125. -/
theorem noS6A_Law1125 : ∀ v : Magma.tupS6A,
    ¬ @Equation1125 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1125) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1125) (by native_decide) v.1 v.2
    ((@Law1125.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1129 takes them (77 nodes). -/
def ordS6A_Law1129 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1129. -/
theorem noS6A_Law1129 : ∀ v : Magma.tupS6A,
    ¬ @Equation1129 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1129) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1129) (by native_decide) v.1 v.2
    ((@Law1129.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1133 takes them (99 nodes). -/
def ordS6A_Law1133 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1133. -/
theorem noS6A_Law1133 : ∀ v : Magma.tupS6A,
    ¬ @Equation1133 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1133) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1133) (by native_decide) v.1 v.2
    ((@Law1133.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1141 takes them (42 nodes). -/
def ordS6A_Law1141 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1141. -/
theorem noS6A_Law1141 : ∀ v : Magma.tupS6A,
    ¬ @Equation1141 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1141) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1141) (by native_decide) v.1 v.2
    ((@Law1141.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1146 takes them (138 nodes). -/
def ordS6A_Law1146 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1146. -/
theorem noS6A_Law1146 : ∀ v : Magma.tupS6A,
    ¬ @Equation1146 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1146) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1146) (by native_decide) v.1 v.2
    ((@Law1146.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1150 takes them (144 nodes). -/
def ordS6A_Law1150 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1150. -/
theorem noS6A_Law1150 : ∀ v : Magma.tupS6A,
    ¬ @Equation1150 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1150) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1150) (by native_decide) v.1 v.2
    ((@Law1150.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1154 takes them (80 nodes). -/
def ordS6A_Law1154 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1154. -/
theorem noS6A_Law1154 : ∀ v : Magma.tupS6A,
    ¬ @Equation1154 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1154) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1154) (by native_decide) v.1 v.2
    ((@Law1154.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1158 takes them (73 nodes). -/
def ordS6A_Law1158 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1158. -/
theorem noS6A_Law1158 : ∀ v : Magma.tupS6A,
    ¬ @Equation1158 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1158) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1158) (by native_decide) v.1 v.2
    ((@Law1158.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1163 takes them (77 nodes). -/
def ordS6A_Law1163 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1163. -/
theorem noS6A_Law1163 : ∀ v : Magma.tupS6A,
    ¬ @Equation1163 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1163) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1163) (by native_decide) v.1 v.2
    ((@Law1163.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1167 takes them (114 nodes). -/
def ordS6A_Law1167 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1167. -/
theorem noS6A_Law1167 : ∀ v : Magma.tupS6A,
    ¬ @Equation1167 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1167) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1167) (by native_decide) v.1 v.2
    ((@Law1167.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1171 takes them (124 nodes). -/
def ordS6A_Law1171 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1171. -/
theorem noS6A_Law1171 : ∀ v : Magma.tupS6A,
    ¬ @Equation1171 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1171) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1171) (by native_decide) v.1 v.2
    ((@Law1171.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1175 takes them (39 nodes). -/
def ordS6A_Law1175 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1175. -/
theorem noS6A_Law1175 : ∀ v : Magma.tupS6A,
    ¬ @Equation1175 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1175) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1175) (by native_decide) v.1 v.2
    ((@Law1175.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1180 takes them (51 nodes). -/
def ordS6A_Law1180 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1180. -/
theorem noS6A_Law1180 : ∀ v : Magma.tupS6A,
    ¬ @Equation1180 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1180) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1180) (by native_decide) v.1 v.2
    ((@Law1180.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1188 takes them (64 nodes). -/
def ordS6A_Law1188 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1188. -/
theorem noS6A_Law1188 : ∀ v : Magma.tupS6A,
    ¬ @Equation1188 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1188) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1188) (by native_decide) v.1 v.2
    ((@Law1188.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1192 takes them (42 nodes). -/
def ordS6A_Law1192 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1192. -/
theorem noS6A_Law1192 : ∀ v : Magma.tupS6A,
    ¬ @Equation1192 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1192) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1192) (by native_decide) v.1 v.2
    ((@Law1192.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1197 takes them (46 nodes). -/
def ordS6A_Law1197 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1197. -/
theorem noS6A_Law1197 : ∀ v : Magma.tupS6A,
    ¬ @Equation1197 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1197) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1197) (by native_decide) v.1 v.2
    ((@Law1197.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `26` equations. -/
theorem srch6A_refutes_9 :
    FamilyRefutes Magma.srch6A [
      1072, 1078, 1082, 1088, 1092, 1096, 1100, 1104, 1115, 1119, 1125, 1129, 1133, 1141, 1146,
      1150, 1154, 1158, 1163, 1167, 1171, 1175, 1180, 1188, 1192, 1197
    ] :=
  ⟨noS6A_Law1072, noS6A_Law1078, noS6A_Law1082, noS6A_Law1088, noS6A_Law1092, noS6A_Law1096, noS6A_Law1100, noS6A_Law1104, noS6A_Law1115, noS6A_Law1119, noS6A_Law1125, noS6A_Law1129, noS6A_Law1133, noS6A_Law1141, noS6A_Law1146, noS6A_Law1150, noS6A_Law1154, noS6A_Law1158, noS6A_Law1163, noS6A_Law1167, noS6A_Law1171, noS6A_Law1175, noS6A_Law1180, noS6A_Law1188, noS6A_Law1192, noS6A_Law1197⟩
