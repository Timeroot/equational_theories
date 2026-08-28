import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 20 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,756 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4435 takes them (2159 nodes). -/
def ordS8R52_Law4435 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4435. -/
theorem noS8R52_Law4435 : ∀ v : Magma.tup8R52,
    ¬ @Equation4435 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4435) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4435) (by native_decide) v.1 v.2
    ((@Law4435.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4445 takes them (326 nodes). -/
def ordS8R52_Law4445 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4445. -/
theorem noS8R52_Law4445 : ∀ v : Magma.tup8R52,
    ¬ @Equation4445 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4445) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4445) (by native_decide) v.1 v.2
    ((@Law4445.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4472 takes them (326 nodes). -/
def ordS8R52_Law4472 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4472. -/
theorem noS8R52_Law4472 : ∀ v : Magma.tup8R52,
    ¬ @Equation4472 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4472) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4472) (by native_decide) v.1 v.2
    ((@Law4472.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (945 nodes). -/
def ordS8R52_Law4585 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4585. -/
theorem noS8R52_Law4585 : ∀ v : Magma.tup8R52,
    ¬ @Equation4585 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R52_refutes_19 :
    FamilyRefutes Magma.srch8R52 [
      4435, 4445, 4472, 4585
    ] :=
  ⟨noS8R52_Law4435, noS8R52_Law4445, noS8R52_Law4472, noS8R52_Law4585⟩
