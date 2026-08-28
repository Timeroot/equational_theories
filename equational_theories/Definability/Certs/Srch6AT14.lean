import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 15 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `19`
equations here, 3,035 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1603 takes them (115 nodes). -/
def ordS6A_Law1603 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1603. -/
theorem noS6A_Law1603 : ∀ v : Magma.tupS6A,
    ¬ @Equation1603 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1603) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1603) (by native_decide) v.1 v.2
    ((@Law1603.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1608 takes them (37 nodes). -/
def ordS6A_Law1608 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1608. -/
theorem noS6A_Law1608 : ∀ v : Magma.tupS6A,
    ¬ @Equation1608 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1608) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1608) (by native_decide) v.1 v.2
    ((@Law1608.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1613 takes them (71 nodes). -/
def ordS6A_Law1613 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1613. -/
theorem noS6A_Law1613 : ∀ v : Magma.tupS6A,
    ¬ @Equation1613 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1613) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1613) (by native_decide) v.1 v.2
    ((@Law1613.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1618 takes them (35 nodes). -/
def ordS6A_Law1618 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1618. -/
theorem noS6A_Law1618 : ∀ v : Magma.tupS6A,
    ¬ @Equation1618 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1618) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1618) (by native_decide) v.1 v.2
    ((@Law1618.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1623 takes them (35 nodes). -/
def ordS6A_Law1623 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1623. -/
theorem noS6A_Law1623 : ∀ v : Magma.tupS6A,
    ¬ @Equation1623 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1623) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1623) (by native_decide) v.1 v.2
    ((@Law1623.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1639 takes them (283 nodes). -/
def ordS6A_Law1639 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1639. -/
theorem noS6A_Law1639 : ∀ v : Magma.tupS6A,
    ¬ @Equation1639 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1639) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1639) (by native_decide) v.1 v.2
    ((@Law1639.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1642 takes them (305 nodes). -/
def ordS6A_Law1642 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1642. -/
theorem noS6A_Law1642 : ∀ v : Magma.tupS6A,
    ¬ @Equation1642 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1642) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1642) (by native_decide) v.1 v.2
    ((@Law1642.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1643 takes them (172 nodes). -/
def ordS6A_Law1643 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1643. -/
theorem noS6A_Law1643 : ∀ v : Magma.tupS6A,
    ¬ @Equation1643 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1643) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1643) (by native_decide) v.1 v.2
    ((@Law1643.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1646 takes them (176 nodes). -/
def ordS6A_Law1646 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1646. -/
theorem noS6A_Law1646 : ∀ v : Magma.tupS6A,
    ¬ @Equation1646 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1646) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1646) (by native_decide) v.1 v.2
    ((@Law1646.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1648 takes them (314 nodes). -/
def ordS6A_Law1648 : List (Fin 11) := [9, 0, 1, 3, 10, 5, 2, 4, 6, 7, 8]

/-- No member of the class satisfies equation 1648. -/
theorem noS6A_Law1648 : ∀ v : Magma.tupS6A,
    ¬ @Equation1648 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1648) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1648) (by native_decide) v.1 v.2
    ((@Law1648.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1649 takes them (72 nodes). -/
def ordS6A_Law1649 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1649. -/
theorem noS6A_Law1649 : ∀ v : Magma.tupS6A,
    ¬ @Equation1649 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1649) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1649) (by native_decide) v.1 v.2
    ((@Law1649.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1651 takes them (143 nodes). -/
def ordS6A_Law1651 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1651. -/
theorem noS6A_Law1651 : ∀ v : Magma.tupS6A,
    ¬ @Equation1651 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1651) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1651) (by native_decide) v.1 v.2
    ((@Law1651.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1652 takes them (135 nodes). -/
def ordS6A_Law1652 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1652. -/
theorem noS6A_Law1652 : ∀ v : Magma.tupS6A,
    ¬ @Equation1652 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1652) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1652) (by native_decide) v.1 v.2
    ((@Law1652.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1653 takes them (55 nodes). -/
def ordS6A_Law1653 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1653. -/
theorem noS6A_Law1653 : ∀ v : Magma.tupS6A,
    ¬ @Equation1653 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1653) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1653) (by native_decide) v.1 v.2
    ((@Law1653.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1656 takes them (157 nodes). -/
def ordS6A_Law1656 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1656. -/
theorem noS6A_Law1656 : ∀ v : Magma.tupS6A,
    ¬ @Equation1656 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1656) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1656) (by native_decide) v.1 v.2
    ((@Law1656.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1659 takes them (200 nodes). -/
def ordS6A_Law1659 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1659. -/
theorem noS6A_Law1659 : ∀ v : Magma.tupS6A,
    ¬ @Equation1659 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1659) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1659) (by native_decide) v.1 v.2
    ((@Law1659.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1660 takes them (337 nodes). -/
def ordS6A_Law1660 : List (Fin 11) := [6, 8, 4, 5, 10, 1, 7, 2, 0, 3, 9]

/-- No member of the class satisfies equation 1660. -/
theorem noS6A_Law1660 : ∀ v : Magma.tupS6A,
    ¬ @Equation1660 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1660) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1660) (by native_decide) v.1 v.2
    ((@Law1660.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1661 takes them (281 nodes). -/
def ordS6A_Law1661 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1661. -/
theorem noS6A_Law1661 : ∀ v : Magma.tupS6A,
    ¬ @Equation1661 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1661) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1661) (by native_decide) v.1 v.2
    ((@Law1661.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1663 takes them (112 nodes). -/
def ordS6A_Law1663 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1663. -/
theorem noS6A_Law1663 : ∀ v : Magma.tupS6A,
    ¬ @Equation1663 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1663) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1663) (by native_decide) v.1 v.2
    ((@Law1663.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `19` equations. -/
theorem srch6A_refutes_14 :
    FamilyRefutes Magma.srch6A [
      1603, 1608, 1613, 1618, 1623, 1639, 1642, 1643, 1646, 1648, 1649, 1651, 1652, 1653, 1656,
      1659, 1660, 1661, 1663
    ] :=
  ⟨noS6A_Law1603, noS6A_Law1608, noS6A_Law1613, noS6A_Law1618, noS6A_Law1623, noS6A_Law1639, noS6A_Law1642, noS6A_Law1643, noS6A_Law1646, noS6A_Law1648, noS6A_Law1649, noS6A_Law1651, noS6A_Law1652, noS6A_Law1653, noS6A_Law1656, noS6A_Law1659, noS6A_Law1660, noS6A_Law1661, noS6A_Law1663⟩
