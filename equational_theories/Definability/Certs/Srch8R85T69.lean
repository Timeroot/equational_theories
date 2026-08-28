import equational_theories.Definability.Srch_S8R85

/-!
# Structural certificate targets: `Magma.srch8R85` (part 70 of 130)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R85_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,019 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R85_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2660 takes them (658 nodes). -/
def ordS8R85_Law2660 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2660. -/
theorem noS8R85_Law2660 : ∀ v : Magma.tup8R85,
    ¬ @Equation2660 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 2)
    (ord := ordS8R85_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2665 takes them (898 nodes). -/
def ordS8R85_Law2665 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2665. -/
theorem noS8R85_Law2665 : ∀ v : Magma.tup8R85,
    ¬ @Equation2665 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2665) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 3)
    (ord := ordS8R85_Law2665) (by native_decide) v.1 v.2
    ((@Law2665.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2688 takes them (238 nodes). -/
def ordS8R85_Law2688 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2688. -/
theorem noS8R85_Law2688 : ∀ v : Magma.tup8R85,
    ¬ @Equation2688 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 3)
    (ord := ordS8R85_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (1225 nodes). -/
def ordS8R85_Law2850 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2850. -/
theorem noS8R85_Law2850 : ∀ v : Magma.tup8R85,
    ¬ @Equation2850 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 2)
    (ord := ordS8R85_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R85_refutes_69 :
    FamilyRefutes Magma.srch8R85 [
      2660, 2665, 2688, 2850
    ] :=
  ⟨noS8R85_Law2660, noS8R85_Law2665, noS8R85_Law2688, noS8R85_Law2850⟩
