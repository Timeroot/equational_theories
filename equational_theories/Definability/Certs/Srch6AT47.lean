import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 48 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `17`
equations here, 3,015 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4144 takes them (53 nodes). -/
def ordS6A_Law4144 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4144. -/
theorem noS6A_Law4144 : ∀ v : Magma.tupS6A,
    ¬ @Equation4144 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4144) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4144) (by native_decide) v.1 v.2
    ((@Law4144.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4145 takes them (58 nodes). -/
def ordS6A_Law4145 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4145. -/
theorem noS6A_Law4145 : ∀ v : Magma.tupS6A,
    ¬ @Equation4145 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4145) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4145) (by native_decide) v.1 v.2
    ((@Law4145.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4147 takes them (53 nodes). -/
def ordS6A_Law4147 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4147. -/
theorem noS6A_Law4147 : ∀ v : Magma.tupS6A,
    ¬ @Equation4147 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4147) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4147) (by native_decide) v.1 v.2
    ((@Law4147.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4148 takes them (53 nodes). -/
def ordS6A_Law4148 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4148. -/
theorem noS6A_Law4148 : ∀ v : Magma.tupS6A,
    ¬ @Equation4148 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4148) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4148) (by native_decide) v.1 v.2
    ((@Law4148.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4149 takes them (54 nodes). -/
def ordS6A_Law4149 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4149. -/
theorem noS6A_Law4149 : ∀ v : Magma.tupS6A,
    ¬ @Equation4149 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4149) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4149) (by native_decide) v.1 v.2
    ((@Law4149.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4150 takes them (223 nodes). -/
def ordS6A_Law4150 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4150. -/
theorem noS6A_Law4150 : ∀ v : Magma.tupS6A,
    ¬ @Equation4150 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4150) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4150) (by native_decide) v.1 v.2
    ((@Law4150.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4151 takes them (49 nodes). -/
def ordS6A_Law4151 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4151. -/
theorem noS6A_Law4151 : ∀ v : Magma.tupS6A,
    ¬ @Equation4151 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4151) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4151) (by native_decide) v.1 v.2
    ((@Law4151.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4152 takes them (49 nodes). -/
def ordS6A_Law4152 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4152. -/
theorem noS6A_Law4152 : ∀ v : Magma.tupS6A,
    ¬ @Equation4152 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4152) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4152) (by native_decide) v.1 v.2
    ((@Law4152.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4153 takes them (49 nodes). -/
def ordS6A_Law4153 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4153. -/
theorem noS6A_Law4153 : ∀ v : Magma.tupS6A,
    ¬ @Equation4153 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4153) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4153) (by native_decide) v.1 v.2
    ((@Law4153.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4154 takes them (547 nodes). -/
def ordS6A_Law4154 : List (Fin 11) := [7, 5, 9, 6, 10, 3, 0, 4, 1, 2, 8]

/-- No member of the class satisfies equation 4154. -/
theorem noS6A_Law4154 : ∀ v : Magma.tupS6A,
    ¬ @Equation4154 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4154) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law4154) (by native_decide) v.1 v.2
    ((@Law4154.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4156 takes them (123 nodes). -/
def ordS6A_Law4156 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4156. -/
theorem noS6A_Law4156 : ∀ v : Magma.tupS6A,
    ¬ @Equation4156 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4156) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4156) (by native_decide) v.1 v.2
    ((@Law4156.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4157 takes them (704 nodes). -/
def ordS6A_Law4157 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4157. -/
theorem noS6A_Law4157 : ∀ v : Magma.tupS6A,
    ¬ @Equation4157 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4157) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law4157) (by native_decide) v.1 v.2
    ((@Law4157.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4159 takes them (141 nodes). -/
def ordS6A_Law4159 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4159. -/
theorem noS6A_Law4159 : ∀ v : Magma.tupS6A,
    ¬ @Equation4159 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4159) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4159) (by native_decide) v.1 v.2
    ((@Law4159.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4160 takes them (183 nodes). -/
def ordS6A_Law4160 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4160. -/
theorem noS6A_Law4160 : ∀ v : Magma.tupS6A,
    ¬ @Equation4160 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4160) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4160) (by native_decide) v.1 v.2
    ((@Law4160.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4161 takes them (261 nodes). -/
def ordS6A_Law4161 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4161. -/
theorem noS6A_Law4161 : ∀ v : Magma.tupS6A,
    ¬ @Equation4161 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4161) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4161) (by native_decide) v.1 v.2
    ((@Law4161.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4162 takes them (307 nodes). -/
def ordS6A_Law4162 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4162. -/
theorem noS6A_Law4162 : ∀ v : Magma.tupS6A,
    ¬ @Equation4162 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4162) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4162) (by native_decide) v.1 v.2
    ((@Law4162.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4163 takes them (108 nodes). -/
def ordS6A_Law4163 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4163. -/
theorem noS6A_Law4163 : ∀ v : Magma.tupS6A,
    ¬ @Equation4163 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4163) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4163) (by native_decide) v.1 v.2
    ((@Law4163.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch6A_refutes_47 :
    FamilyRefutes Magma.srch6A [
      4144, 4145, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4154, 4156, 4157, 4159, 4160, 4161,
      4162, 4163
    ] :=
  ⟨noS6A_Law4144, noS6A_Law4145, noS6A_Law4147, noS6A_Law4148, noS6A_Law4149, noS6A_Law4150, noS6A_Law4151, noS6A_Law4152, noS6A_Law4153, noS6A_Law4154, noS6A_Law4156, noS6A_Law4157, noS6A_Law4159, noS6A_Law4160, noS6A_Law4161, noS6A_Law4162, noS6A_Law4163⟩
