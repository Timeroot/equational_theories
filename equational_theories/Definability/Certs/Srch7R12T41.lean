import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 42 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 3,419 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3902 takes them (351 nodes). -/
def ordS7R12_Law3902 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3902. -/
theorem noS7R12_Law3902 : ∀ v : Magma.tup7R12,
    ¬ @Equation3902 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3902) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3902) (by native_decide) v.1 v.2
    ((@Law3902.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3904 takes them (93 nodes). -/
def ordS7R12_Law3904 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3904. -/
theorem noS7R12_Law3904 : ∀ v : Magma.tup7R12,
    ¬ @Equation3904 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3904) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3904) (by native_decide) v.1 v.2
    ((@Law3904.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3909 takes them (50 nodes). -/
def ordS7R12_Law3909 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3909. -/
theorem noS7R12_Law3909 : ∀ v : Magma.tup7R12,
    ¬ @Equation3909 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3909) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3909) (by native_decide) v.1 v.2
    ((@Law3909.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3910 takes them (198 nodes). -/
def ordS7R12_Law3910 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3910. -/
theorem noS7R12_Law3910 : ∀ v : Magma.tup7R12,
    ¬ @Equation3910 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3910) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3910) (by native_decide) v.1 v.2
    ((@Law3910.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3912 takes them (88 nodes). -/
def ordS7R12_Law3912 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3912. -/
theorem noS7R12_Law3912 : ∀ v : Magma.tup7R12,
    ¬ @Equation3912 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3912) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3912) (by native_decide) v.1 v.2
    ((@Law3912.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (464 nodes). -/
def ordS7R12_Law3917 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3917. -/
theorem noS7R12_Law3917 : ∀ v : Magma.tup7R12,
    ¬ @Equation3917 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (471 nodes). -/
def ordS7R12_Law3924 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3924. -/
theorem noS7R12_Law3924 : ∀ v : Magma.tup7R12,
    ¬ @Equation3924 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3927 takes them (456 nodes). -/
def ordS7R12_Law3927 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3927. -/
theorem noS7R12_Law3927 : ∀ v : Magma.tup7R12,
    ¬ @Equation3927 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3927) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3927) (by native_decide) v.1 v.2
    ((@Law3927.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3930 takes them (92 nodes). -/
def ordS7R12_Law3930 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3930. -/
theorem noS7R12_Law3930 : ∀ v : Magma.tup7R12,
    ¬ @Equation3930 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3930) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3930) (by native_decide) v.1 v.2
    ((@Law3930.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (218 nodes). -/
def ordS7R12_Law3931 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3931. -/
theorem noS7R12_Law3931 : ∀ v : Magma.tup7R12,
    ¬ @Equation3931 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3935 takes them (444 nodes). -/
def ordS7R12_Law3935 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3935. -/
theorem noS7R12_Law3935 : ∀ v : Magma.tup7R12,
    ¬ @Equation3935 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3935) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3935) (by native_decide) v.1 v.2
    ((@Law3935.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3939 takes them (105 nodes). -/
def ordS7R12_Law3939 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3939. -/
theorem noS7R12_Law3939 : ∀ v : Magma.tup7R12,
    ¬ @Equation3939 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3939) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3939) (by native_decide) v.1 v.2
    ((@Law3939.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3947 takes them (88 nodes). -/
def ordS7R12_Law3947 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3947. -/
theorem noS7R12_Law3947 : ∀ v : Magma.tup7R12,
    ¬ @Equation3947 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3947) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3947) (by native_decide) v.1 v.2
    ((@Law3947.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3951 takes them (301 nodes). -/
def ordS7R12_Law3951 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3951. -/
theorem noS7R12_Law3951 : ∀ v : Magma.tup7R12,
    ¬ @Equation3951 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3951) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3951) (by native_decide) v.1 v.2
    ((@Law3951.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch7R12_refutes_41 :
    FamilyRefutes Magma.srch7R12 [
      3902, 3904, 3909, 3910, 3912, 3917, 3924, 3927, 3930, 3931, 3935, 3939, 3947, 3951
    ] :=
  ⟨noS7R12_Law3902, noS7R12_Law3904, noS7R12_Law3909, noS7R12_Law3910, noS7R12_Law3912, noS7R12_Law3917, noS7R12_Law3924, noS7R12_Law3927, noS7R12_Law3930, noS7R12_Law3931, noS7R12_Law3935, noS7R12_Law3939, noS7R12_Law3947, noS7R12_Law3951⟩
