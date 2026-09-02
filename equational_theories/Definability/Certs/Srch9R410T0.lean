import equational_theories.Definability.Srch_S9R410

/-!
# Structural certificate targets: `Magma.srch9R410`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R410_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 283 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R410_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 452 takes them (80 nodes). -/
def ordS9R410_Law452 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 452. -/
theorem noS9R410_Law452 : ∀ v : Magma.tup9R410,
    ¬ @Equation452 (Fin 9) (Magma.srch9R410 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law452) (E := S9R410.E) (tr := S9R410.tr) (z := S9R410.z)
    (st := S9R410.st) (X := S9R410.X) (envs := Magma.envsRed 9 S9R410.E 3)
    (ord := ordS9R410_Law452) (by native_decide) v.1 v.2
    ((@Law452.models_iff (Fin 9) (Magma.srch9R410 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3201 takes them (154 nodes). -/
def ordS9R410_Law3201 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3201. -/
theorem noS9R410_Law3201 : ∀ v : Magma.tup9R410,
    ¬ @Equation3201 (Fin 9) (Magma.srch9R410 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3201) (E := S9R410.E) (tr := S9R410.tr) (z := S9R410.z)
    (st := S9R410.st) (X := S9R410.X) (envs := Magma.envsRed 9 S9R410.E 3)
    (ord := ordS9R410_Law3201) (by native_decide) v.1 v.2
    ((@Law3201.models_iff (Fin 9) (Magma.srch9R410 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3675 takes them (31 nodes). -/
def ordS9R410_Law3675 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3675. -/
theorem noS9R410_Law3675 : ∀ v : Magma.tup9R410,
    ¬ @Equation3675 (Fin 9) (Magma.srch9R410 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3675) (E := S9R410.E) (tr := S9R410.tr) (z := S9R410.z)
    (st := S9R410.st) (X := S9R410.X) (envs := Magma.envsRed 9 S9R410.E 2)
    (ord := ordS9R410_Law3675) (by native_decide) v.1 v.2
    ((@Law3675.models_iff (Fin 9) (Magma.srch9R410 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3703 takes them (18 nodes). -/
def ordS9R410_Law3703 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3703. -/
theorem noS9R410_Law3703 : ∀ v : Magma.tup9R410,
    ¬ @Equation3703 (Fin 9) (Magma.srch9R410 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3703) (E := S9R410.E) (tr := S9R410.tr) (z := S9R410.z)
    (st := S9R410.st) (X := S9R410.X) (envs := Magma.envsRed 9 S9R410.E 3)
    (ord := ordS9R410_Law3703) (by native_decide) v.1 v.2
    ((@Law3703.models_iff (Fin 9) (Magma.srch9R410 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch9R410_refutes_0 :
    FamilyRefutes Magma.srch9R410 [
      452, 3201, 3675, 3703
    ] :=
  ⟨noS9R410_Law452, noS9R410_Law3201, noS9R410_Law3675, noS9R410_Law3703⟩
