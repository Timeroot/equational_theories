import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 106 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `9`
equations here, 3,526 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1665 takes them (383 nodes). -/
def ordS8R2_Law1665 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1665. -/
theorem noS8R2_Law1665 : ∀ v : Magma.tup8R2,
    ¬ @Equation1665 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1665) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1665) (by native_decide) v.1 v.2
    ((@Law1665.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1666 takes them (355 nodes). -/
def ordS8R2_Law1666 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1666. -/
theorem noS8R2_Law1666 : ∀ v : Magma.tup8R2,
    ¬ @Equation1666 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1666) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1666) (by native_decide) v.1 v.2
    ((@Law1666.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1667 takes them (71 nodes). -/
def ordS8R2_Law1667 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1667. -/
theorem noS8R2_Law1667 : ∀ v : Magma.tup8R2,
    ¬ @Equation1667 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1667) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1667) (by native_decide) v.1 v.2
    ((@Law1667.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1669 takes them (356 nodes). -/
def ordS8R2_Law1669 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1669. -/
theorem noS8R2_Law1669 : ∀ v : Magma.tup8R2,
    ¬ @Equation1669 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1669) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1669) (by native_decide) v.1 v.2
    ((@Law1669.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1670 takes them (1053 nodes). -/
def ordS8R2_Law1670 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1670. -/
theorem noS8R2_Law1670 : ∀ v : Magma.tup8R2,
    ¬ @Equation1670 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1670) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1670) (by native_decide) v.1 v.2
    ((@Law1670.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1671 takes them (71 nodes). -/
def ordS8R2_Law1671 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1671. -/
theorem noS8R2_Law1671 : ∀ v : Magma.tup8R2,
    ¬ @Equation1671 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1671) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1671) (by native_decide) v.1 v.2
    ((@Law1671.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1673 takes them (811 nodes). -/
def ordS8R2_Law1673 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1673. -/
theorem noS8R2_Law1673 : ∀ v : Magma.tup8R2,
    ¬ @Equation1673 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1673) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1673) (by native_decide) v.1 v.2
    ((@Law1673.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1674 takes them (355 nodes). -/
def ordS8R2_Law1674 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1674. -/
theorem noS8R2_Law1674 : ∀ v : Magma.tup8R2,
    ¬ @Equation1674 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1674) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1674) (by native_decide) v.1 v.2
    ((@Law1674.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1675 takes them (71 nodes). -/
def ordS8R2_Law1675 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1675. -/
theorem noS8R2_Law1675 : ∀ v : Magma.tup8R2,
    ¬ @Equation1675 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1675) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1675) (by native_decide) v.1 v.2
    ((@Law1675.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch8R2_refutes_105 :
    FamilyRefutes Magma.srch8R2 [
      1665, 1666, 1667, 1669, 1670, 1671, 1673, 1674, 1675
    ] :=
  ⟨noS8R2_Law1665, noS8R2_Law1666, noS8R2_Law1667, noS8R2_Law1669, noS8R2_Law1670, noS8R2_Law1671, noS8R2_Law1673, noS8R2_Law1674, noS8R2_Law1675⟩
