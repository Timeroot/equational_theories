import equational_theories.Definability.Srch_S7R8

/-!
# Structural certificate targets: `Magma.srch7R8` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R8_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `14`
equations here, 2,778 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R8_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3583 takes them (106 nodes). -/
def ordS7R8_Law3583 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3583. -/
theorem noS7R8_Law3583 : ∀ v : Magma.tup7R8,
    ¬ @Equation3583 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3583) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3583) (by native_decide) v.1 v.2
    ((@Law3583.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3716 takes them (133 nodes). -/
def ordS7R8_Law3716 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3716. -/
theorem noS7R8_Law3716 : ∀ v : Magma.tup7R8,
    ¬ @Equation3716 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3716) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3716) (by native_decide) v.1 v.2
    ((@Law3716.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3790 takes them (172 nodes). -/
def ordS7R8_Law3790 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3790. -/
theorem noS7R8_Law3790 : ∀ v : Magma.tup7R8,
    ¬ @Equation3790 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3790) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3790) (by native_decide) v.1 v.2
    ((@Law3790.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3929 takes them (94 nodes). -/
def ordS7R8_Law3929 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3929. -/
theorem noS7R8_Law3929 : ∀ v : Magma.tup7R8,
    ¬ @Equation3929 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3929) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3929) (by native_decide) v.1 v.2
    ((@Law3929.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3930 takes them (144 nodes). -/
def ordS7R8_Law3930 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3930. -/
theorem noS7R8_Law3930 : ∀ v : Magma.tup7R8,
    ¬ @Equation3930 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3930) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3930) (by native_decide) v.1 v.2
    ((@Law3930.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3939 takes them (257 nodes). -/
def ordS7R8_Law3939 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3939. -/
theorem noS7R8_Law3939 : ∀ v : Magma.tup7R8,
    ¬ @Equation3939 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3939) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3939) (by native_decide) v.1 v.2
    ((@Law3939.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3947 takes them (231 nodes). -/
def ordS7R8_Law3947 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3947. -/
theorem noS7R8_Law3947 : ∀ v : Magma.tup7R8,
    ¬ @Equation3947 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3947) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 4)
    (ord := ordS7R8_Law3947) (by native_decide) v.1 v.2
    ((@Law3947.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (255 nodes). -/
def ordS7R8_Law3972 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3972. -/
theorem noS7R8_Law3972 : ∀ v : Magma.tup7R8,
    ¬ @Equation3972 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (301 nodes). -/
def ordS7R8_Law3989 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3989. -/
theorem noS7R8_Law3989 : ∀ v : Magma.tup7R8,
    ¬ @Equation3989 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (253 nodes). -/
def ordS7R8_Law3997 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3997. -/
theorem noS7R8_Law3997 : ∀ v : Magma.tup7R8,
    ¬ @Equation3997 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (215 nodes). -/
def ordS7R8_Law4040 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4040. -/
theorem noS7R8_Law4040 : ∀ v : Magma.tup7R8,
    ¬ @Equation4040 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 4)
    (ord := ordS7R8_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (223 nodes). -/
def ordS7R8_Law4200 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4200. -/
theorem noS7R8_Law4200 : ∀ v : Magma.tup7R8,
    ¬ @Equation4200 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4209 takes them (197 nodes). -/
def ordS7R8_Law4209 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4209. -/
theorem noS7R8_Law4209 : ∀ v : Magma.tup7R8,
    ¬ @Equation4209 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4209) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law4209) (by native_decide) v.1 v.2
    ((@Law4209.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (197 nodes). -/
def ordS7R8_Law4243 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4243. -/
theorem noS7R8_Law4243 : ∀ v : Magma.tup7R8,
    ¬ @Equation4243 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 4)
    (ord := ordS7R8_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch7R8_refutes_1 :
    FamilyRefutes Magma.srch7R8 [
      3583, 3716, 3790, 3929, 3930, 3939, 3947, 3972, 3989, 3997, 4040, 4200, 4209, 4243
    ] :=
  ⟨noS7R8_Law3583, noS7R8_Law3716, noS7R8_Law3790, noS7R8_Law3929, noS7R8_Law3930, noS7R8_Law3939, noS7R8_Law3947, noS7R8_Law3972, noS7R8_Law3989, noS7R8_Law3997, noS7R8_Law4040, noS7R8_Law4200, noS7R8_Law4209, noS7R8_Law4243⟩
