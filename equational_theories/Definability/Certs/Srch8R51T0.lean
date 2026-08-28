import equational_theories.Definability.Srch_S8R51

/-!
# Structural certificate targets: `Magma.srch8R51` (part 1 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R51_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,644 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R51_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 430 takes them (1127 nodes). -/
def ordS8R51_Law430 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 430. -/
theorem noS8R51_Law430 : ∀ v : Magma.tup8R51,
    ¬ @Equation430 (Fin 8) (Magma.srch8R51 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S8R51.E) (tr := S8R51.tr) (z := S8R51.z)
    (st := S8R51.st) (X := S8R51.X) (envs := Magma.envsRed 8 S8R51.E 2)
    (ord := ordS8R51_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 8) (Magma.srch8R51 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 630 takes them (1204 nodes). -/
def ordS8R51_Law630 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 630. -/
theorem noS8R51_Law630 : ∀ v : Magma.tup8R51,
    ¬ @Equation630 (Fin 8) (Magma.srch8R51 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law630) (E := S8R51.E) (tr := S8R51.tr) (z := S8R51.z)
    (st := S8R51.st) (X := S8R51.X) (envs := Magma.envsRed 8 S8R51.E 2)
    (ord := ordS8R51_Law630) (by native_decide) v.1 v.2
    ((@Law630.models_iff (Fin 8) (Magma.srch8R51 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 834 takes them (190 nodes). -/
def ordS8R51_Law834 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 834. -/
theorem noS8R51_Law834 : ∀ v : Magma.tup8R51,
    ¬ @Equation834 (Fin 8) (Magma.srch8R51 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law834) (E := S8R51.E) (tr := S8R51.tr) (z := S8R51.z)
    (st := S8R51.st) (X := S8R51.X) (envs := Magma.envsRed 8 S8R51.E 3)
    (ord := ordS8R51_Law834) (by native_decide) v.1 v.2
    ((@Law834.models_iff (Fin 8) (Magma.srch8R51 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (1123 nodes). -/
def ordS8R51_Law843 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 843. -/
theorem noS8R51_Law843 : ∀ v : Magma.tup8R51,
    ¬ @Equation843 (Fin 8) (Magma.srch8R51 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := S8R51.E) (tr := S8R51.tr) (z := S8R51.z)
    (st := S8R51.st) (X := S8R51.X) (envs := Magma.envsRed 8 S8R51.E 2)
    (ord := ordS8R51_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 8) (Magma.srch8R51 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R51_refutes_0 :
    FamilyRefutes Magma.srch8R51 [
      430, 630, 834, 843
    ] :=
  ⟨noS8R51_Law430, noS8R51_Law630, noS8R51_Law834, noS8R51_Law843⟩
