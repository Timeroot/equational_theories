import equational_theories.Definability.Srch_S8R108

/-!
# Structural certificate targets: `Magma.srch8R108` (part 2 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R108_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,559 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R108_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3604 takes them (2087 nodes). -/
def ordS8R108_Law3604 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 3604. -/
theorem noS8R108_Law3604 : ∀ v : Magma.tup8R108,
    ¬ @Equation3604 (Fin 8) (Magma.srch8R108 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3604) (E := S8R108.E) (tr := S8R108.tr) (z := S8R108.z)
    (st := S8R108.st) (X := S8R108.X) (envs := Magma.envsRed 8 S8R108.E 3)
    (ord := ordS8R108_Law3604) (by native_decide) v.1 v.2
    ((@Law3604.models_iff (Fin 8) (Magma.srch8R108 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3711 takes them (506 nodes). -/
def ordS8R108_Law3711 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 3711. -/
theorem noS8R108_Law3711 : ∀ v : Magma.tup8R108,
    ¬ @Equation3711 (Fin 8) (Magma.srch8R108 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3711) (E := S8R108.E) (tr := S8R108.tr) (z := S8R108.z)
    (st := S8R108.st) (X := S8R108.X) (envs := Magma.envsRed 8 S8R108.E 2)
    (ord := ordS8R108_Law3711) (by native_decide) v.1 v.2
    ((@Law3711.models_iff (Fin 8) (Magma.srch8R108 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3713 takes them (478 nodes). -/
def ordS8R108_Law3713 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 3713. -/
theorem noS8R108_Law3713 : ∀ v : Magma.tup8R108,
    ¬ @Equation3713 (Fin 8) (Magma.srch8R108 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3713) (E := S8R108.E) (tr := S8R108.tr) (z := S8R108.z)
    (st := S8R108.st) (X := S8R108.X) (envs := Magma.envsRed 8 S8R108.E 3)
    (ord := ordS8R108_Law3713) (by native_decide) v.1 v.2
    ((@Law3713.models_iff (Fin 8) (Magma.srch8R108 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3717 takes them (488 nodes). -/
def ordS8R108_Law3717 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 3717. -/
theorem noS8R108_Law3717 : ∀ v : Magma.tup8R108,
    ¬ @Equation3717 (Fin 8) (Magma.srch8R108 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3717) (E := S8R108.E) (tr := S8R108.tr) (z := S8R108.z)
    (st := S8R108.st) (X := S8R108.X) (envs := Magma.envsRed 8 S8R108.E 3)
    (ord := ordS8R108_Law3717) (by native_decide) v.1 v.2
    ((@Law3717.models_iff (Fin 8) (Magma.srch8R108 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R108_refutes_1 :
    FamilyRefutes Magma.srch8R108 [
      3604, 3711, 3713, 3717
    ] :=
  ⟨noS8R108_Law3604, noS8R108_Law3711, noS8R108_Law3713, noS8R108_Law3717⟩
