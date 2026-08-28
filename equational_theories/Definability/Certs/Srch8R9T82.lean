import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 83 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `9`
equations here, 3,580 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1608 takes them (360 nodes). -/
def ordS8R9_Law1608 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1608. -/
theorem noS8R9_Law1608 : ∀ v : Magma.tup8R9,
    ¬ @Equation1608 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1608) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1608) (by native_decide) v.1 v.2
    ((@Law1608.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1613 takes them (358 nodes). -/
def ordS8R9_Law1613 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1613. -/
theorem noS8R9_Law1613 : ∀ v : Magma.tup8R9,
    ¬ @Equation1613 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1613) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1613) (by native_decide) v.1 v.2
    ((@Law1613.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1618 takes them (741 nodes). -/
def ordS8R9_Law1618 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1618. -/
theorem noS8R9_Law1618 : ∀ v : Magma.tup8R9,
    ¬ @Equation1618 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1618) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1618) (by native_decide) v.1 v.2
    ((@Law1618.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1623 takes them (11 nodes). -/
def ordS8R9_Law1623 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1623. -/
theorem noS8R9_Law1623 : ∀ v : Magma.tup8R9,
    ¬ @Equation1623 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1623) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law1623) (by native_decide) v.1 v.2
    ((@Law1623.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1636 takes them (480 nodes). -/
def ordS8R9_Law1636 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1636. -/
theorem noS8R9_Law1636 : ∀ v : Magma.tup8R9,
    ¬ @Equation1636 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1636) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law1636) (by native_decide) v.1 v.2
    ((@Law1636.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1639 takes them (49 nodes). -/
def ordS8R9_Law1639 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1639. -/
theorem noS8R9_Law1639 : ∀ v : Magma.tup8R9,
    ¬ @Equation1639 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1639) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law1639) (by native_decide) v.1 v.2
    ((@Law1639.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1641 takes them (764 nodes). -/
def ordS8R9_Law1641 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1641. -/
theorem noS8R9_Law1641 : ∀ v : Magma.tup8R9,
    ¬ @Equation1641 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1641) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law1641) (by native_decide) v.1 v.2
    ((@Law1641.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1642 takes them (768 nodes). -/
def ordS8R9_Law1642 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1642. -/
theorem noS8R9_Law1642 : ∀ v : Magma.tup8R9,
    ¬ @Equation1642 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1642) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law1642) (by native_decide) v.1 v.2
    ((@Law1642.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1643 takes them (49 nodes). -/
def ordS8R9_Law1643 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1643. -/
theorem noS8R9_Law1643 : ∀ v : Magma.tup8R9,
    ¬ @Equation1643 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1643) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1643) (by native_decide) v.1 v.2
    ((@Law1643.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch8R9_refutes_82 :
    FamilyRefutes Magma.srch8R9 [
      1608, 1613, 1618, 1623, 1636, 1639, 1641, 1642, 1643
    ] :=
  ⟨noS8R9_Law1608, noS8R9_Law1613, noS8R9_Law1618, noS8R9_Law1623, noS8R9_Law1636, noS8R9_Law1639, noS8R9_Law1641, noS8R9_Law1642, noS8R9_Law1643⟩
