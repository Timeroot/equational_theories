import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 177 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `4`
equations here, 2,750 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3100 takes them (776 nodes). -/
def ordS8R9_Law3100 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3100. -/
theorem noS8R9_Law3100 : ∀ v : Magma.tup8R9,
    ¬ @Equation3100 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3100) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3100) (by native_decide) v.1 v.2
    ((@Law3100.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3101 takes them (65 nodes). -/
def ordS8R9_Law3101 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3101. -/
theorem noS8R9_Law3101 : ∀ v : Magma.tup8R9,
    ¬ @Equation3101 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3101) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3101) (by native_decide) v.1 v.2
    ((@Law3101.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3118 takes them (1153 nodes). -/
def ordS8R9_Law3118 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3118. -/
theorem noS8R9_Law3118 : ∀ v : Magma.tup8R9,
    ¬ @Equation3118 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3118) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3118) (by native_decide) v.1 v.2
    ((@Law3118.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3126 takes them (756 nodes). -/
def ordS8R9_Law3126 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3126. -/
theorem noS8R9_Law3126 : ∀ v : Magma.tup8R9,
    ¬ @Equation3126 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3126) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3126) (by native_decide) v.1 v.2
    ((@Law3126.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R9_refutes_176 :
    FamilyRefutes Magma.srch8R9 [
      3100, 3101, 3118, 3126
    ] :=
  ⟨noS8R9_Law3100, noS8R9_Law3101, noS8R9_Law3118, noS8R9_Law3126⟩
