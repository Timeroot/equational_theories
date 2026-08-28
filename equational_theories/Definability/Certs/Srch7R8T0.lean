import equational_theories.Definability.Srch_S7R8

/-!
# Structural certificate targets: `Magma.srch7R8` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R8_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `16`
equations here, 3,323 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R8_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 327 takes them (179 nodes). -/
def ordS7R8_Law327 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 327. -/
theorem noS7R8_Law327 : ∀ v : Magma.tup7R8,
    ¬ @Equation327 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law327) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law327) (by native_decide) v.1 v.2
    ((@Law327.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 395 takes them (197 nodes). -/
def ordS7R8_Law395 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 395. -/
theorem noS7R8_Law395 : ∀ v : Magma.tup7R8,
    ¬ @Equation395 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law395) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law395) (by native_decide) v.1 v.2
    ((@Law395.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 676 takes them (189 nodes). -/
def ordS7R8_Law676 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 676. -/
theorem noS7R8_Law676 : ∀ v : Magma.tup7R8,
    ¬ @Equation676 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law676) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 2)
    (ord := ordS7R8_Law676) (by native_decide) v.1 v.2
    ((@Law676.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1694 takes them (170 nodes). -/
def ordS7R8_Law1694 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1694. -/
theorem noS7R8_Law1694 : ∀ v : Magma.tup7R8,
    ¬ @Equation1694 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1694) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 2)
    (ord := ordS7R8_Law1694) (by native_decide) v.1 v.2
    ((@Law1694.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1858 takes them (271 nodes). -/
def ordS7R8_Law1858 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1858. -/
theorem noS7R8_Law1858 : ∀ v : Magma.tup7R8,
    ¬ @Equation1858 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1858) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 2)
    (ord := ordS7R8_Law1858) (by native_decide) v.1 v.2
    ((@Law1858.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2853 takes them (155 nodes). -/
def ordS7R8_Law2853 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2853. -/
theorem noS7R8_Law2853 : ∀ v : Magma.tup7R8,
    ¬ @Equation2853 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2853) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 2)
    (ord := ordS7R8_Law2853) (by native_decide) v.1 v.2
    ((@Law2853.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3317 takes them (179 nodes). -/
def ordS7R8_Law3317 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3317. -/
theorem noS7R8_Law3317 : ∀ v : Magma.tup7R8,
    ¬ @Equation3317 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3317) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3317) (by native_decide) v.1 v.2
    ((@Law3317.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (179 nodes). -/
def ordS7R8_Law3324 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3324. -/
theorem noS7R8_Law3324 : ∀ v : Magma.tup7R8,
    ¬ @Equation3324 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 4)
    (ord := ordS7R8_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (249 nodes). -/
def ordS7R8_Law3331 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3331. -/
theorem noS7R8_Law3331 : ∀ v : Magma.tup7R8,
    ¬ @Equation3331 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3515 takes them (239 nodes). -/
def ordS7R8_Law3515 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3515. -/
theorem noS7R8_Law3515 : ∀ v : Magma.tup7R8,
    ¬ @Equation3515 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3515) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3515) (by native_decide) v.1 v.2
    ((@Law3515.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (308 nodes). -/
def ordS7R8_Law3523 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3523. -/
theorem noS7R8_Law3523 : ∀ v : Magma.tup7R8,
    ¬ @Equation3523 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (245 nodes). -/
def ordS7R8_Law3524 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3524. -/
theorem noS7R8_Law3524 : ∀ v : Magma.tup7R8,
    ¬ @Equation3524 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (190 nodes). -/
def ordS7R8_Law3527 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3527. -/
theorem noS7R8_Law3527 : ∀ v : Magma.tup7R8,
    ¬ @Equation3527 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 4)
    (ord := ordS7R8_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (210 nodes). -/
def ordS7R8_Law3534 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3534. -/
theorem noS7R8_Law3534 : ∀ v : Magma.tup7R8,
    ¬ @Equation3534 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3541 takes them (208 nodes). -/
def ordS7R8_Law3541 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3541. -/
theorem noS7R8_Law3541 : ∀ v : Magma.tup7R8,
    ¬ @Equation3541 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3541) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 4)
    (ord := ordS7R8_Law3541) (by native_decide) v.1 v.2
    ((@Law3541.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3566 takes them (155 nodes). -/
def ordS7R8_Law3566 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3566. -/
theorem noS7R8_Law3566 : ∀ v : Magma.tup7R8,
    ¬ @Equation3566 (Fin 7) (Magma.srch7R8 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3566) (E := S7R8.E) (tr := S7R8.tr) (z := S7R8.z)
    (st := S7R8.st) (X := S7R8.X) (envs := Magma.envsRed 7 S7R8.E 3)
    (ord := ordS7R8_Law3566) (by native_decide) v.1 v.2
    ((@Law3566.models_iff (Fin 7) (Magma.srch7R8 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch7R8_refutes_0 :
    FamilyRefutes Magma.srch7R8 [
      327, 395, 676, 1694, 1858, 2853, 3317, 3324, 3331, 3515, 3523, 3524, 3527, 3534, 3541, 3566
    ] :=
  ⟨noS7R8_Law327, noS7R8_Law395, noS7R8_Law676, noS7R8_Law1694, noS7R8_Law1858, noS7R8_Law2853, noS7R8_Law3317, noS7R8_Law3324, noS7R8_Law3331, noS7R8_Law3515, noS7R8_Law3523, noS7R8_Law3524, noS7R8_Law3527, noS7R8_Law3534, noS7R8_Law3541, noS7R8_Law3566⟩
