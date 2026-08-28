import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 16 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `20`
equations here, 3,112 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1665 takes them (188 nodes). -/
def ordS6A_Law1665 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1665. -/
theorem noS6A_Law1665 : ∀ v : Magma.tupS6A,
    ¬ @Equation1665 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1665) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1665) (by native_decide) v.1 v.2
    ((@Law1665.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1666 takes them (172 nodes). -/
def ordS6A_Law1666 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1666. -/
theorem noS6A_Law1666 : ∀ v : Magma.tupS6A,
    ¬ @Equation1666 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1666) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1666) (by native_decide) v.1 v.2
    ((@Law1666.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1667 takes them (99 nodes). -/
def ordS6A_Law1667 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1667. -/
theorem noS6A_Law1667 : ∀ v : Magma.tupS6A,
    ¬ @Equation1667 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1667) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1667) (by native_decide) v.1 v.2
    ((@Law1667.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1668 takes them (395 nodes). -/
def ordS6A_Law1668 : List (Fin 11) := [5, 8, 4, 1, 2, 10, 0, 6, 7, 9, 3]

/-- No member of the class satisfies equation 1668. -/
theorem noS6A_Law1668 : ∀ v : Magma.tupS6A,
    ¬ @Equation1668 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1668) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1668) (by native_decide) v.1 v.2
    ((@Law1668.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1669 takes them (80 nodes). -/
def ordS6A_Law1669 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1669. -/
theorem noS6A_Law1669 : ∀ v : Magma.tupS6A,
    ¬ @Equation1669 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1669) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1669) (by native_decide) v.1 v.2
    ((@Law1669.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1670 takes them (269 nodes). -/
def ordS6A_Law1670 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1670. -/
theorem noS6A_Law1670 : ∀ v : Magma.tupS6A,
    ¬ @Equation1670 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1670) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1670) (by native_decide) v.1 v.2
    ((@Law1670.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1671 takes them (41 nodes). -/
def ordS6A_Law1671 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1671. -/
theorem noS6A_Law1671 : ∀ v : Magma.tupS6A,
    ¬ @Equation1671 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1671) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1671) (by native_decide) v.1 v.2
    ((@Law1671.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1674 takes them (149 nodes). -/
def ordS6A_Law1674 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1674. -/
theorem noS6A_Law1674 : ∀ v : Magma.tupS6A,
    ¬ @Equation1674 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1674) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1674) (by native_decide) v.1 v.2
    ((@Law1674.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1675 takes them (129 nodes). -/
def ordS6A_Law1675 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1675. -/
theorem noS6A_Law1675 : ∀ v : Magma.tupS6A,
    ¬ @Equation1675 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1675) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1675) (by native_decide) v.1 v.2
    ((@Law1675.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1676 takes them (169 nodes). -/
def ordS6A_Law1676 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1676. -/
theorem noS6A_Law1676 : ∀ v : Magma.tupS6A,
    ¬ @Equation1676 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1676) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1676) (by native_decide) v.1 v.2
    ((@Law1676.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1677 takes them (65 nodes). -/
def ordS6A_Law1677 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1677. -/
theorem noS6A_Law1677 : ∀ v : Magma.tupS6A,
    ¬ @Equation1677 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1677) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1677) (by native_decide) v.1 v.2
    ((@Law1677.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1678 takes them (97 nodes). -/
def ordS6A_Law1678 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1678. -/
theorem noS6A_Law1678 : ∀ v : Magma.tupS6A,
    ¬ @Equation1678 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1678) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1678) (by native_decide) v.1 v.2
    ((@Law1678.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1679 takes them (60 nodes). -/
def ordS6A_Law1679 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1679. -/
theorem noS6A_Law1679 : ∀ v : Magma.tupS6A,
    ¬ @Equation1679 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1679) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1679) (by native_decide) v.1 v.2
    ((@Law1679.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1680 takes them (40 nodes). -/
def ordS6A_Law1680 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1680. -/
theorem noS6A_Law1680 : ∀ v : Magma.tupS6A,
    ¬ @Equation1680 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1680) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1680) (by native_decide) v.1 v.2
    ((@Law1680.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1694 takes them (527 nodes). -/
def ordS6A_Law1694 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1694. -/
theorem noS6A_Law1694 : ∀ v : Magma.tupS6A,
    ¬ @Equation1694 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1694) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1694) (by native_decide) v.1 v.2
    ((@Law1694.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1697 takes them (88 nodes). -/
def ordS6A_Law1697 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1697. -/
theorem noS6A_Law1697 : ∀ v : Magma.tupS6A,
    ¬ @Equation1697 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1697) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1697) (by native_decide) v.1 v.2
    ((@Law1697.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1705 takes them (161 nodes). -/
def ordS6A_Law1705 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1705. -/
theorem noS6A_Law1705 : ∀ v : Magma.tupS6A,
    ¬ @Equation1705 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1705) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1705) (by native_decide) v.1 v.2
    ((@Law1705.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1709 takes them (183 nodes). -/
def ordS6A_Law1709 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1709. -/
theorem noS6A_Law1709 : ∀ v : Magma.tupS6A,
    ¬ @Equation1709 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1709) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1709) (by native_decide) v.1 v.2
    ((@Law1709.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1713 takes them (61 nodes). -/
def ordS6A_Law1713 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1713. -/
theorem noS6A_Law1713 : ∀ v : Magma.tupS6A,
    ¬ @Equation1713 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1713) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1713) (by native_decide) v.1 v.2
    ((@Law1713.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1734 takes them (139 nodes). -/
def ordS6A_Law1734 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1734. -/
theorem noS6A_Law1734 : ∀ v : Magma.tupS6A,
    ¬ @Equation1734 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1734) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1734) (by native_decide) v.1 v.2
    ((@Law1734.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch6A_refutes_15 :
    FamilyRefutes Magma.srch6A [
      1665, 1666, 1667, 1668, 1669, 1670, 1671, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1694,
      1697, 1705, 1709, 1713, 1734
    ] :=
  ⟨noS6A_Law1665, noS6A_Law1666, noS6A_Law1667, noS6A_Law1668, noS6A_Law1669, noS6A_Law1670, noS6A_Law1671, noS6A_Law1674, noS6A_Law1675, noS6A_Law1676, noS6A_Law1677, noS6A_Law1678, noS6A_Law1679, noS6A_Law1680, noS6A_Law1694, noS6A_Law1697, noS6A_Law1705, noS6A_Law1709, noS6A_Law1713, noS6A_Law1734⟩
