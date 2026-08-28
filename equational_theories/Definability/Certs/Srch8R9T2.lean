import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 3 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `20`
equations here, 3,171 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 120 takes them (768 nodes). -/
def ordS8R9_Law120 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 120. -/
theorem noS8R9_Law120 : ∀ v : Magma.tup8R9,
    ¬ @Equation120 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law120) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law120) (by native_decide) v.1 v.2
    ((@Law120.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 130 takes them (91 nodes). -/
def ordS8R9_Law130 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 130. -/
theorem noS8R9_Law130 : ∀ v : Magma.tup8R9,
    ¬ @Equation130 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law130) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law130) (by native_decide) v.1 v.2
    ((@Law130.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 134 takes them (764 nodes). -/
def ordS8R9_Law134 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 134. -/
theorem noS8R9_Law134 : ∀ v : Magma.tup8R9,
    ¬ @Equation134 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law134) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law134) (by native_decide) v.1 v.2
    ((@Law134.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 142 takes them (49 nodes). -/
def ordS8R9_Law142 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 142. -/
theorem noS8R9_Law142 : ∀ v : Magma.tup8R9,
    ¬ @Equation142 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law142) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law142) (by native_decide) v.1 v.2
    ((@Law142.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 146 takes them (49 nodes). -/
def ordS8R9_Law146 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 146. -/
theorem noS8R9_Law146 : ∀ v : Magma.tup8R9,
    ¬ @Equation146 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law146) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law146) (by native_decide) v.1 v.2
    ((@Law146.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 154 takes them (49 nodes). -/
def ordS8R9_Law154 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 154. -/
theorem noS8R9_Law154 : ∀ v : Magma.tup8R9,
    ¬ @Equation154 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law154) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law154) (by native_decide) v.1 v.2
    ((@Law154.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 155 takes them (49 nodes). -/
def ordS8R9_Law155 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 155. -/
theorem noS8R9_Law155 : ∀ v : Magma.tup8R9,
    ¬ @Equation155 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law155) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law155) (by native_decide) v.1 v.2
    ((@Law155.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 157 takes them (49 nodes). -/
def ordS8R9_Law157 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 157. -/
theorem noS8R9_Law157 : ∀ v : Magma.tup8R9,
    ¬ @Equation157 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law157) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law157) (by native_decide) v.1 v.2
    ((@Law157.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 158 takes them (49 nodes). -/
def ordS8R9_Law158 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 158. -/
theorem noS8R9_Law158 : ∀ v : Magma.tup8R9,
    ¬ @Equation158 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law158) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law158) (by native_decide) v.1 v.2
    ((@Law158.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 163 takes them (49 nodes). -/
def ordS8R9_Law163 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 163. -/
theorem noS8R9_Law163 : ∀ v : Magma.tup8R9,
    ¬ @Equation163 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law163) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law163) (by native_decide) v.1 v.2
    ((@Law163.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 164 takes them (49 nodes). -/
def ordS8R9_Law164 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 164. -/
theorem noS8R9_Law164 : ∀ v : Magma.tup8R9,
    ¬ @Equation164 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law164) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law164) (by native_decide) v.1 v.2
    ((@Law164.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 165 takes them (49 nodes). -/
def ordS8R9_Law165 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 165. -/
theorem noS8R9_Law165 : ∀ v : Magma.tup8R9,
    ¬ @Equation165 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law165) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law165) (by native_decide) v.1 v.2
    ((@Law165.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 169 takes them (49 nodes). -/
def ordS8R9_Law169 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 169. -/
theorem noS8R9_Law169 : ∀ v : Magma.tup8R9,
    ¬ @Equation169 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law169) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law169) (by native_decide) v.1 v.2
    ((@Law169.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 172 takes them (49 nodes). -/
def ordS8R9_Law172 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 172. -/
theorem noS8R9_Law172 : ∀ v : Magma.tup8R9,
    ¬ @Equation172 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law172) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law172) (by native_decide) v.1 v.2
    ((@Law172.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 176 takes them (49 nodes). -/
def ordS8R9_Law176 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 176. -/
theorem noS8R9_Law176 : ∀ v : Magma.tup8R9,
    ¬ @Equation176 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law176) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law176) (by native_decide) v.1 v.2
    ((@Law176.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 182 takes them (49 nodes). -/
def ordS8R9_Law182 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 182. -/
theorem noS8R9_Law182 : ∀ v : Magma.tup8R9,
    ¬ @Equation182 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law182) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law182) (by native_decide) v.1 v.2
    ((@Law182.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 186 takes them (49 nodes). -/
def ordS8R9_Law186 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 186. -/
theorem noS8R9_Law186 : ∀ v : Magma.tup8R9,
    ¬ @Equation186 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law186) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law186) (by native_decide) v.1 v.2
    ((@Law186.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 190 takes them (49 nodes). -/
def ordS8R9_Law190 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 190. -/
theorem noS8R9_Law190 : ∀ v : Magma.tup8R9,
    ¬ @Equation190 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law190) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law190) (by native_decide) v.1 v.2
    ((@Law190.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 198 takes them (49 nodes). -/
def ordS8R9_Law198 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 198. -/
theorem noS8R9_Law198 : ∀ v : Magma.tup8R9,
    ¬ @Equation198 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law198) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law198) (by native_decide) v.1 v.2
    ((@Law198.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 207 takes them (764 nodes). -/
def ordS8R9_Law207 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 207. -/
theorem noS8R9_Law207 : ∀ v : Magma.tup8R9,
    ¬ @Equation207 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law207) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law207) (by native_decide) v.1 v.2
    ((@Law207.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch8R9_refutes_2 :
    FamilyRefutes Magma.srch8R9 [
      120, 130, 134, 142, 146, 154, 155, 157, 158, 163, 164, 165, 169, 172, 176, 182, 186, 190,
      198, 207
    ] :=
  ⟨noS8R9_Law120, noS8R9_Law130, noS8R9_Law134, noS8R9_Law142, noS8R9_Law146, noS8R9_Law154, noS8R9_Law155, noS8R9_Law157, noS8R9_Law158, noS8R9_Law163, noS8R9_Law164, noS8R9_Law165, noS8R9_Law169, noS8R9_Law172, noS8R9_Law176, noS8R9_Law182, noS8R9_Law186, noS8R9_Law190, noS8R9_Law198, noS8R9_Law207⟩
