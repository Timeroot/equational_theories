import equational_theories.Definability.Srch_S8R43

/-!
# Structural certificate targets: `Magma.srch8R43` (part 2 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R43_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 2,746 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R43_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2376 takes them (213 nodes). -/
def ordS8R43_Law2376 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2376. -/
theorem noS8R43_Law2376 : ∀ v : Magma.tup8R43,
    ¬ @Equation2376 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2376) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law2376) (by native_decide) v.1 v.2
    ((@Law2376.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (286 nodes). -/
def ordS8R43_Law2778 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2778. -/
theorem noS8R43_Law2778 : ∀ v : Magma.tup8R43,
    ¬ @Equation2778 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2782 takes them (219 nodes). -/
def ordS8R43_Law2782 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2782. -/
theorem noS8R43_Law2782 : ∀ v : Magma.tup8R43,
    ¬ @Equation2782 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2782) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law2782) (by native_decide) v.1 v.2
    ((@Law2782.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (332 nodes). -/
def ordS8R43_Law3324 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3324. -/
theorem noS8R43_Law3324 : ∀ v : Magma.tup8R43,
    ¬ @Equation3324 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (392 nodes). -/
def ordS8R43_Law3520 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3520. -/
theorem noS8R43_Law3520 : ∀ v : Magma.tup8R43,
    ¬ @Equation3520 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (444 nodes). -/
def ordS8R43_Law3523 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3523. -/
theorem noS8R43_Law3523 : ∀ v : Magma.tup8R43,
    ¬ @Equation3523 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (530 nodes). -/
def ordS8R43_Law3524 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3524. -/
theorem noS8R43_Law3524 : ∀ v : Magma.tup8R43,
    ¬ @Equation3524 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (330 nodes). -/
def ordS8R43_Law3527 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3527. -/
theorem noS8R43_Law3527 : ∀ v : Magma.tup8R43,
    ¬ @Equation3527 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch8R43_refutes_1 :
    FamilyRefutes Magma.srch8R43 [
      2376, 2778, 2782, 3324, 3520, 3523, 3524, 3527
    ] :=
  ⟨noS8R43_Law2376, noS8R43_Law2778, noS8R43_Law2782, noS8R43_Law3324, noS8R43_Law3520, noS8R43_Law3523, noS8R43_Law3524, noS8R43_Law3527⟩
