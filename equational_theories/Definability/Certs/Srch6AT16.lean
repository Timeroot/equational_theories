import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 17 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `26`
equations here, 2,937 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1742 takes them (205 nodes). -/
def ordS6A_Law1742 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1742. -/
theorem noS6A_Law1742 : ∀ v : Magma.tupS6A,
    ¬ @Equation1742 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1742) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1742) (by native_decide) v.1 v.2
    ((@Law1742.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1750 takes them (137 nodes). -/
def ordS6A_Law1750 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1750. -/
theorem noS6A_Law1750 : ∀ v : Magma.tupS6A,
    ¬ @Equation1750 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1750) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1750) (by native_decide) v.1 v.2
    ((@Law1750.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1755 takes them (231 nodes). -/
def ordS6A_Law1755 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1755. -/
theorem noS6A_Law1755 : ∀ v : Magma.tupS6A,
    ¬ @Equation1755 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1755) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1755) (by native_decide) v.1 v.2
    ((@Law1755.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1759 takes them (148 nodes). -/
def ordS6A_Law1759 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1759. -/
theorem noS6A_Law1759 : ∀ v : Magma.tupS6A,
    ¬ @Equation1759 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1759) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1759) (by native_decide) v.1 v.2
    ((@Law1759.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1763 takes them (145 nodes). -/
def ordS6A_Law1763 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1763. -/
theorem noS6A_Law1763 : ∀ v : Magma.tupS6A,
    ¬ @Equation1763 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1763) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1763) (by native_decide) v.1 v.2
    ((@Law1763.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1767 takes them (79 nodes). -/
def ordS6A_Law1767 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1767. -/
theorem noS6A_Law1767 : ∀ v : Magma.tupS6A,
    ¬ @Equation1767 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1767) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1767) (by native_decide) v.1 v.2
    ((@Law1767.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1772 takes them (84 nodes). -/
def ordS6A_Law1772 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1772. -/
theorem noS6A_Law1772 : ∀ v : Magma.tupS6A,
    ¬ @Equation1772 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1772) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1772) (by native_decide) v.1 v.2
    ((@Law1772.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1776 takes them (127 nodes). -/
def ordS6A_Law1776 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1776. -/
theorem noS6A_Law1776 : ∀ v : Magma.tupS6A,
    ¬ @Equation1776 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1776) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1776) (by native_decide) v.1 v.2
    ((@Law1776.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1784 takes them (48 nodes). -/
def ordS6A_Law1784 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1784. -/
theorem noS6A_Law1784 : ∀ v : Magma.tupS6A,
    ¬ @Equation1784 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1784) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1784) (by native_decide) v.1 v.2
    ((@Law1784.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1789 takes them (128 nodes). -/
def ordS6A_Law1789 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1789. -/
theorem noS6A_Law1789 : ∀ v : Magma.tupS6A,
    ¬ @Equation1789 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1789) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1789) (by native_decide) v.1 v.2
    ((@Law1789.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1797 takes them (193 nodes). -/
def ordS6A_Law1797 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1797. -/
theorem noS6A_Law1797 : ∀ v : Magma.tupS6A,
    ¬ @Equation1797 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1797) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1797) (by native_decide) v.1 v.2
    ((@Law1797.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1801 takes them (76 nodes). -/
def ordS6A_Law1801 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1801. -/
theorem noS6A_Law1801 : ∀ v : Magma.tupS6A,
    ¬ @Equation1801 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1801) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1801) (by native_decide) v.1 v.2
    ((@Law1801.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1806 takes them (57 nodes). -/
def ordS6A_Law1806 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1806. -/
theorem noS6A_Law1806 : ∀ v : Magma.tupS6A,
    ¬ @Equation1806 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1806) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1806) (by native_decide) v.1 v.2
    ((@Law1806.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1811 takes them (76 nodes). -/
def ordS6A_Law1811 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1811. -/
theorem noS6A_Law1811 : ∀ v : Magma.tupS6A,
    ¬ @Equation1811 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1811) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1811) (by native_decide) v.1 v.2
    ((@Law1811.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1816 takes them (65 nodes). -/
def ordS6A_Law1816 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1816. -/
theorem noS6A_Law1816 : ∀ v : Magma.tupS6A,
    ¬ @Equation1816 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1816) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1816) (by native_decide) v.1 v.2
    ((@Law1816.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1821 takes them (116 nodes). -/
def ordS6A_Law1821 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1821. -/
theorem noS6A_Law1821 : ∀ v : Magma.tupS6A,
    ¬ @Equation1821 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1821) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1821) (by native_decide) v.1 v.2
    ((@Law1821.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1826 takes them (43 nodes). -/
def ordS6A_Law1826 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1826. -/
theorem noS6A_Law1826 : ∀ v : Magma.tupS6A,
    ¬ @Equation1826 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1826) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1826) (by native_decide) v.1 v.2
    ((@Law1826.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1836 takes them (146 nodes). -/
def ordS6A_Law1836 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1836. -/
theorem noS6A_Law1836 : ∀ v : Magma.tupS6A,
    ¬ @Equation1836 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1836) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1836) (by native_decide) v.1 v.2
    ((@Law1836.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1842 takes them (72 nodes). -/
def ordS6A_Law1842 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1842. -/
theorem noS6A_Law1842 : ∀ v : Magma.tupS6A,
    ¬ @Equation1842 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1842) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1842) (by native_decide) v.1 v.2
    ((@Law1842.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1844 takes them (115 nodes). -/
def ordS6A_Law1844 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1844. -/
theorem noS6A_Law1844 : ∀ v : Magma.tupS6A,
    ¬ @Equation1844 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1844) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1844) (by native_decide) v.1 v.2
    ((@Law1844.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1846 takes them (65 nodes). -/
def ordS6A_Law1846 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1846. -/
theorem noS6A_Law1846 : ∀ v : Magma.tupS6A,
    ¬ @Equation1846 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1846) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1846) (by native_decide) v.1 v.2
    ((@Law1846.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1852 takes them (81 nodes). -/
def ordS6A_Law1852 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1852. -/
theorem noS6A_Law1852 : ∀ v : Magma.tupS6A,
    ¬ @Equation1852 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1852) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1852) (by native_decide) v.1 v.2
    ((@Law1852.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1854 takes them (116 nodes). -/
def ordS6A_Law1854 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1854. -/
theorem noS6A_Law1854 : ∀ v : Magma.tupS6A,
    ¬ @Equation1854 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1854) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1854) (by native_decide) v.1 v.2
    ((@Law1854.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1856 takes them (65 nodes). -/
def ordS6A_Law1856 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1856. -/
theorem noS6A_Law1856 : ∀ v : Magma.tupS6A,
    ¬ @Equation1856 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1856) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1856) (by native_decide) v.1 v.2
    ((@Law1856.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1858 takes them (189 nodes). -/
def ordS6A_Law1858 : List (Fin 11) := [8, 0, 6, 7, 5, 4, 1, 9, 3, 10, 2]

/-- No member of the class satisfies equation 1858. -/
theorem noS6A_Law1858 : ∀ v : Magma.tupS6A,
    ¬ @Equation1858 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1858) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1858) (by native_decide) v.1 v.2
    ((@Law1858.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1859 takes them (130 nodes). -/
def ordS6A_Law1859 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1859. -/
theorem noS6A_Law1859 : ∀ v : Magma.tupS6A,
    ¬ @Equation1859 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1859) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1859) (by native_decide) v.1 v.2
    ((@Law1859.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `26` equations. -/
theorem srch6A_refutes_16 :
    FamilyRefutes Magma.srch6A [
      1742, 1750, 1755, 1759, 1763, 1767, 1772, 1776, 1784, 1789, 1797, 1801, 1806, 1811, 1816,
      1821, 1826, 1836, 1842, 1844, 1846, 1852, 1854, 1856, 1858, 1859
    ] :=
  ⟨noS6A_Law1742, noS6A_Law1750, noS6A_Law1755, noS6A_Law1759, noS6A_Law1763, noS6A_Law1767, noS6A_Law1772, noS6A_Law1776, noS6A_Law1784, noS6A_Law1789, noS6A_Law1797, noS6A_Law1801, noS6A_Law1806, noS6A_Law1811, noS6A_Law1816, noS6A_Law1821, noS6A_Law1826, noS6A_Law1836, noS6A_Law1842, noS6A_Law1844, noS6A_Law1846, noS6A_Law1852, noS6A_Law1854, noS6A_Law1856, noS6A_Law1858, noS6A_Law1859⟩
