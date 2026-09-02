import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 165 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 2,739 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2881 takes them (33 nodes). -/
def ordS9R2000_Law2881 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2881. -/
theorem noS9R2000_Law2881 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2881 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2881) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2881) (by native_decide) v.1 v.2
    ((@Law2881.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2885 takes them (505 nodes). -/
def ordS9R2000_Law2885 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2885. -/
theorem noS9R2000_Law2885 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2885 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2885) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2885) (by native_decide) v.1 v.2
    ((@Law2885.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2889 takes them (43 nodes). -/
def ordS9R2000_Law2889 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2889. -/
theorem noS9R2000_Law2889 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2889 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2889) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2889) (by native_decide) v.1 v.2
    ((@Law2889.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2893 takes them (33 nodes). -/
def ordS9R2000_Law2893 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2893. -/
theorem noS9R2000_Law2893 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2893 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2893) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2893) (by native_decide) v.1 v.2
    ((@Law2893.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2895 takes them (2125 nodes). -/
def ordS9R2000_Law2895 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2895. -/
theorem noS9R2000_Law2895 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2895 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2895) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2895) (by native_decide) v.1 v.2
    ((@Law2895.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch9R2000_refutes_164 :
    FamilyRefutes Magma.srch9R2000 [
      2881, 2885, 2889, 2893, 2895
    ] :=
  ⟨noS9R2000_Law2881, noS9R2000_Law2885, noS9R2000_Law2889, noS9R2000_Law2893, noS9R2000_Law2895⟩
