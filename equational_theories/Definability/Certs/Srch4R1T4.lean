import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 5 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 3,304 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1560 takes them (253 nodes). -/
def ordS4R1_Law1560 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1560. -/
theorem noS4R1_Law1560 : ∀ v : Magma.tup4R1,
    ¬ @Equation1560 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1560) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1560) (by native_decide) v.1 v.2
    ((@Law1560.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1586 takes them (238 nodes). -/
def ordS4R1_Law1586 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1586. -/
theorem noS4R1_Law1586 : ∀ v : Magma.tup4R1,
    ¬ @Equation1586 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1586) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1586) (by native_decide) v.1 v.2
    ((@Law1586.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1594 takes them (205 nodes). -/
def ordS4R1_Law1594 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1594. -/
theorem noS4R1_Law1594 : ∀ v : Magma.tup4R1,
    ¬ @Equation1594 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1594) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1594) (by native_decide) v.1 v.2
    ((@Law1594.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1648 takes them (579 nodes). -/
def ordS4R1_Law1648 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1648. -/
theorem noS4R1_Law1648 : ∀ v : Magma.tup4R1,
    ¬ @Equation1648 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1648) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1648) (by native_decide) v.1 v.2
    ((@Law1648.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1656 takes them (391 nodes). -/
def ordS4R1_Law1656 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1656. -/
theorem noS4R1_Law1656 : ∀ v : Magma.tup4R1,
    ¬ @Equation1656 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1656) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1656) (by native_decide) v.1 v.2
    ((@Law1656.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1659 takes them (275 nodes). -/
def ordS4R1_Law1659 : List (Fin 8) := [1, 5, 4, 0, 7, 6, 2, 3]

/-- No member of the class satisfies equation 1659. -/
theorem noS4R1_Law1659 : ∀ v : Magma.tup4R1,
    ¬ @Equation1659 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1659) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1659) (by native_decide) v.1 v.2
    ((@Law1659.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1661 takes them (391 nodes). -/
def ordS4R1_Law1661 : List (Fin 8) := [0, 4, 2, 1, 5, 7, 6, 3]

/-- No member of the class satisfies equation 1661. -/
theorem noS4R1_Law1661 : ∀ v : Magma.tup4R1,
    ¬ @Equation1661 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1661) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1661) (by native_decide) v.1 v.2
    ((@Law1661.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1663 takes them (284 nodes). -/
def ordS4R1_Law1663 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1663. -/
theorem noS4R1_Law1663 : ∀ v : Magma.tup4R1,
    ¬ @Equation1663 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1663) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law1663) (by native_decide) v.1 v.2
    ((@Law1663.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1742 takes them (277 nodes). -/
def ordS4R1_Law1742 : List (Fin 8) := [5, 2, 7, 0, 1, 4, 6, 3]

/-- No member of the class satisfies equation 1742. -/
theorem noS4R1_Law1742 : ∀ v : Magma.tup4R1,
    ¬ @Equation1742 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1742) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1742) (by native_decide) v.1 v.2
    ((@Law1742.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1763 takes them (411 nodes). -/
def ordS4R1_Law1763 : List (Fin 8) := [4, 7, 5, 3, 0, 6, 1, 2]

/-- No member of the class satisfies equation 1763. -/
theorem noS4R1_Law1763 : ∀ v : Magma.tup4R1,
    ¬ @Equation1763 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1763) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1763) (by native_decide) v.1 v.2
    ((@Law1763.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch4R1_refutes_4 :
    FamilyRefutes Magma.srch4R1 [
      1560, 1586, 1594, 1648, 1656, 1659, 1661, 1663, 1742, 1763
    ] :=
  ⟨noS4R1_Law1560, noS4R1_Law1586, noS4R1_Law1594, noS4R1_Law1648, noS4R1_Law1656, noS4R1_Law1659, noS4R1_Law1661, noS4R1_Law1663, noS4R1_Law1742, noS4R1_Law1763⟩
