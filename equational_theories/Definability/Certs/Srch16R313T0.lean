import equational_theories.Definability.Srch_S16R313

/-!
# Structural certificate targets: `Magma.srch16R313`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S16R313_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `24` equations here, 150 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S16R313_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 635 takes them (8 nodes). -/
def ordS16R313_Law635 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 635. -/
theorem noS16R313_Law635 : ∀ v : Magma.tup16R313,
    ¬ @Equation635 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law635) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law635) (by native_decide) v.1 v.2
    ((@Law635.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 645 takes them (8 nodes). -/
def ordS16R313_Law645 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 645. -/
theorem noS16R313_Law645 : ∀ v : Magma.tup16R313,
    ¬ @Equation645 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law645) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law645) (by native_decide) v.1 v.2
    ((@Law645.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 824 takes them (4 nodes). -/
def ordS16R313_Law824 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 824. -/
theorem noS16R313_Law824 : ∀ v : Magma.tup16R313,
    ¬ @Equation824 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law824) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law824) (by native_decide) v.1 v.2
    ((@Law824.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 828 takes them (6 nodes). -/
def ordS16R313_Law828 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 828. -/
theorem noS16R313_Law828 : ∀ v : Magma.tup16R313,
    ¬ @Equation828 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law828) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law828) (by native_decide) v.1 v.2
    ((@Law828.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 838 takes them (8 nodes). -/
def ordS16R313_Law838 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 838. -/
theorem noS16R313_Law838 : ∀ v : Magma.tup16R313,
    ¬ @Equation838 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law838) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law838) (by native_decide) v.1 v.2
    ((@Law838.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 856 takes them (8 nodes). -/
def ordS16R313_Law856 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 856. -/
theorem noS16R313_Law856 : ∀ v : Magma.tup16R313,
    ¬ @Equation856 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law856) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law856) (by native_decide) v.1 v.2
    ((@Law856.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1027 takes them (4 nodes). -/
def ordS16R313_Law1027 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1027. -/
theorem noS16R313_Law1027 : ∀ v : Magma.tup16R313,
    ¬ @Equation1027 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1027) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law1027) (by native_decide) v.1 v.2
    ((@Law1027.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2513 takes them (4 nodes). -/
def ordS16R313_Law2513 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2513. -/
theorem noS16R313_Law2513 : ∀ v : Magma.tup16R313,
    ¬ @Equation2513 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2513) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2513) (by native_decide) v.1 v.2
    ((@Law2513.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2665 takes them (8 nodes). -/
def ordS16R313_Law2665 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2665. -/
theorem noS16R313_Law2665 : ∀ v : Magma.tup16R313,
    ¬ @Equation2665 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2665) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2665) (by native_decide) v.1 v.2
    ((@Law2665.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2679 takes them (6 nodes). -/
def ordS16R313_Law2679 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2679. -/
theorem noS16R313_Law2679 : ∀ v : Magma.tup16R313,
    ¬ @Equation2679 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2679) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2679) (by native_decide) v.1 v.2
    ((@Law2679.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2683 takes them (8 nodes). -/
def ordS16R313_Law2683 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2683. -/
theorem noS16R313_Law2683 : ∀ v : Magma.tup16R313,
    ¬ @Equation2683 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2683) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2683) (by native_decide) v.1 v.2
    ((@Law2683.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2716 takes them (4 nodes). -/
def ordS16R313_Law2716 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2716. -/
theorem noS16R313_Law2716 : ∀ v : Magma.tup16R313,
    ¬ @Equation2716 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2716) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2716) (by native_decide) v.1 v.2
    ((@Law2716.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2868 takes them (8 nodes). -/
def ordS16R313_Law2868 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2868. -/
theorem noS16R313_Law2868 : ∀ v : Magma.tup16R313,
    ¬ @Equation2868 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2868) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2868) (by native_decide) v.1 v.2
    ((@Law2868.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2890 takes them (8 nodes). -/
def ordS16R313_Law2890 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2890. -/
theorem noS16R313_Law2890 : ∀ v : Magma.tup16R313,
    ¬ @Equation2890 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2890) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 3)
    (ord := ordS16R313_Law2890) (by native_decide) v.1 v.2
    ((@Law2890.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (6 nodes). -/
def ordS16R313_Law3308 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3308. -/
theorem noS16R313_Law3308 : ∀ v : Magma.tup16R313,
    ¬ @Equation3308 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (5 nodes). -/
def ordS16R313_Law3343 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3343. -/
theorem noS16R313_Law3343 : ∀ v : Magma.tup16R313,
    ¬ @Equation3343 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (6 nodes). -/
def ordS16R313_Law3511 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3511. -/
theorem noS16R313_Law3511 : ∀ v : Magma.tup16R313,
    ¬ @Equation3511 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (6 nodes). -/
def ordS16R313_Law3955 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3955. -/
theorem noS16R313_Law3955 : ∀ v : Magma.tup16R313,
    ¬ @Equation3955 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (5 nodes). -/
def ordS16R313_Law4130 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4130. -/
theorem noS16R313_Law4130 : ∀ v : Magma.tup16R313,
    ¬ @Equation4130 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (6 nodes). -/
def ordS16R313_Law4158 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4158. -/
theorem noS16R313_Law4158 : ∀ v : Magma.tup16R313,
    ¬ @Equation4158 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (6 nodes). -/
def ordS16R313_Law4283 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4283. -/
theorem noS16R313_Law4283 : ∀ v : Magma.tup16R313,
    ¬ @Equation4283 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (6 nodes). -/
def ordS16R313_Law4291 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4291. -/
theorem noS16R313_Law4291 : ∀ v : Magma.tup16R313,
    ¬ @Equation4291 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (6 nodes). -/
def ordS16R313_Law4629 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4629. -/
theorem noS16R313_Law4629 : ∀ v : Magma.tup16R313,
    ¬ @Equation4629 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (6 nodes). -/
def ordS16R313_Law4635 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4635. -/
theorem noS16R313_Law4635 : ∀ v : Magma.tup16R313,
    ¬ @Equation4635 (Fin 16) (Magma.srch16R313 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S16R313.E) (tr := S16R313.tr) (z := S16R313.z)
    (st := S16R313.st) (X := S16R313.X) (envs := Magma.envsRed 16 S16R313.E 2)
    (ord := ordS16R313_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 16) (Magma.srch16R313 v)).mpr hv)

/-- No member of the class satisfies any of these `24` equations. -/
theorem srch16R313_refutes_0 :
    FamilyRefutes Magma.srch16R313 [
      635, 645, 824, 828, 838, 856, 1027, 2513, 2665, 2679, 2683, 2716, 2868, 2890, 3308, 3343,
      3511, 3955, 4130, 4158, 4283, 4291, 4629, 4635
    ] :=
  ⟨noS16R313_Law635, noS16R313_Law645, noS16R313_Law824, noS16R313_Law828, noS16R313_Law838, noS16R313_Law856, noS16R313_Law1027, noS16R313_Law2513, noS16R313_Law2665, noS16R313_Law2679, noS16R313_Law2683, noS16R313_Law2716, noS16R313_Law2868, noS16R313_Law2890, noS16R313_Law3308, noS16R313_Law3343, noS16R313_Law3511, noS16R313_Law3955, noS16R313_Law4130, noS16R313_Law4158, noS16R313_Law4283, noS16R313_Law4291, noS16R313_Law4629, noS16R313_Law4635⟩
