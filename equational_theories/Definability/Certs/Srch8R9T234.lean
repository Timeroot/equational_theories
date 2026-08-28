import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 235 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 1,922 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4148 takes them (768 nodes). -/
def ordS8R9_Law4148 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4148. -/
theorem noS8R9_Law4148 : ∀ v : Magma.tup8R9,
    ¬ @Equation4148 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4148) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4148) (by native_decide) v.1 v.2
    ((@Law4148.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4149 takes them (55 nodes). -/
def ordS8R9_Law4149 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4149. -/
theorem noS8R9_Law4149 : ∀ v : Magma.tup8R9,
    ¬ @Equation4149 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4149) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4149) (by native_decide) v.1 v.2
    ((@Law4149.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4151 takes them (53 nodes). -/
def ordS8R9_Law4151 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4151. -/
theorem noS8R9_Law4151 : ∀ v : Magma.tup8R9,
    ¬ @Equation4151 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4151) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4151) (by native_decide) v.1 v.2
    ((@Law4151.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4152 takes them (768 nodes). -/
def ordS8R9_Law4152 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4152. -/
theorem noS8R9_Law4152 : ∀ v : Magma.tup8R9,
    ¬ @Equation4152 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4152) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4152) (by native_decide) v.1 v.2
    ((@Law4152.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4153 takes them (50 nodes). -/
def ordS8R9_Law4153 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4153. -/
theorem noS8R9_Law4153 : ∀ v : Magma.tup8R9,
    ¬ @Equation4153 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4153) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law4153) (by native_decide) v.1 v.2
    ((@Law4153.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4161 takes them (101 nodes). -/
def ordS8R9_Law4161 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4161. -/
theorem noS8R9_Law4161 : ∀ v : Magma.tup8R9,
    ¬ @Equation4161 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4161) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4161) (by native_decide) v.1 v.2
    ((@Law4161.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4171 takes them (127 nodes). -/
def ordS8R9_Law4171 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4171. -/
theorem noS8R9_Law4171 : ∀ v : Magma.tup8R9,
    ¬ @Equation4171 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4171) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4171) (by native_decide) v.1 v.2
    ((@Law4171.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R9_refutes_234 :
    FamilyRefutes Magma.srch8R9 [
      4148, 4149, 4151, 4152, 4153, 4161, 4171
    ] :=
  ⟨noS8R9_Law4148, noS8R9_Law4149, noS8R9_Law4151, noS8R9_Law4152, noS8R9_Law4153, noS8R9_Law4161, noS8R9_Law4171⟩
