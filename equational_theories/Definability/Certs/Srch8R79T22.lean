import equational_theories.Definability.Srch_S8R79

/-!
# Structural certificate targets: `Magma.srch8R79` (part 23 of 33)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R79_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 2,670 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R79_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2485 takes them (1061 nodes). -/
def ordS8R79_Law2485 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2485. -/
theorem noS8R79_Law2485 : ∀ v : Magma.tup8R79,
    ¬ @Equation2485 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2647 takes them (686 nodes). -/
def ordS8R79_Law2647 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2647. -/
theorem noS8R79_Law2647 : ∀ v : Magma.tup8R79,
    ¬ @Equation2647 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2647) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 2)
    (ord := ordS8R79_Law2647) (by native_decide) v.1 v.2
    ((@Law2647.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2660 takes them (646 nodes). -/
def ordS8R79_Law2660 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2660. -/
theorem noS8R79_Law2660 : ∀ v : Magma.tup8R79,
    ¬ @Equation2660 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 2)
    (ord := ordS8R79_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2688 takes them (195 nodes). -/
def ordS8R79_Law2688 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2688. -/
theorem noS8R79_Law2688 : ∀ v : Magma.tup8R79,
    ¬ @Equation2688 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2712 takes them (82 nodes). -/
def ordS8R79_Law2712 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2712. -/
theorem noS8R79_Law2712 : ∀ v : Magma.tup8R79,
    ¬ @Equation2712 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2712) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law2712) (by native_decide) v.1 v.2
    ((@Law2712.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch8R79_refutes_22 :
    FamilyRefutes Magma.srch8R79 [
      2485, 2647, 2660, 2688, 2712
    ] :=
  ⟨noS8R79_Law2485, noS8R79_Law2647, noS8R79_Law2660, noS8R79_Law2688, noS8R79_Law2712⟩
