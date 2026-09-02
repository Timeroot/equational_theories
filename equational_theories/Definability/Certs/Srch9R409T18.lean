import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 19 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,264 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2878 takes them (716 nodes). -/
def ordS9R409_Law2878 : List (Fin 12) := [4, 8, 9, 7, 11, 0, 10, 5, 1, 2, 3, 6]

/-- No member of the class satisfies equation 2878. -/
theorem noS9R409_Law2878 : ∀ v : Magma.tup9R409,
    ¬ @Equation2878 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2878) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2878) (by native_decide) v.1 v.2
    ((@Law2878.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2886 takes them (1070 nodes). -/
def ordS9R409_Law2886 : List (Fin 12) := [10, 5, 3, 0, 11, 8, 2, 6, 4, 7, 9, 1]

/-- No member of the class satisfies equation 2886. -/
theorem noS9R409_Law2886 : ∀ v : Magma.tup9R409,
    ¬ @Equation2886 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2886) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2886) (by native_decide) v.1 v.2
    ((@Law2886.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2890 takes them (1053 nodes). -/
def ordS9R409_Law2890 : List (Fin 12) := [2, 5, 8, 9, 4, 11, 0, 6, 7, 10, 3, 1]

/-- No member of the class satisfies equation 2890. -/
theorem noS9R409_Law2890 : ∀ v : Magma.tup9R409,
    ¬ @Equation2890 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2890) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law2890) (by native_decide) v.1 v.2
    ((@Law2890.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2894 takes them (425 nodes). -/
def ordS9R409_Law2894 : List (Fin 12) := [11, 6, 10, 9, 8, 5, 4, 7, 2, 3, 0, 1]

/-- No member of the class satisfies equation 2894. -/
theorem noS9R409_Law2894 : ∀ v : Magma.tup9R409,
    ¬ @Equation2894 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2894) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 4)
    (ord := ordS9R409_Law2894) (by native_decide) v.1 v.2
    ((@Law2894.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch9R409_refutes_18 :
    FamilyRefutes Magma.srch9R409 [
      2878, 2886, 2890, 2894
    ] :=
  ⟨noS9R409_Law2878, noS9R409_Law2886, noS9R409_Law2890, noS9R409_Law2894⟩
