import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 14 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `23`
equations here, 3,065 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1491 takes them (309 nodes). -/
def ordS6A_Law1491 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1491. -/
theorem noS6A_Law1491 : ∀ v : Magma.tupS6A,
    ¬ @Equation1491 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1491) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1491) (by native_decide) v.1 v.2
    ((@Law1491.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1494 takes them (52 nodes). -/
def ordS6A_Law1494 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1494. -/
theorem noS6A_Law1494 : ∀ v : Magma.tupS6A,
    ¬ @Equation1494 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1494) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1494) (by native_decide) v.1 v.2
    ((@Law1494.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1498 takes them (201 nodes). -/
def ordS6A_Law1498 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1498. -/
theorem noS6A_Law1498 : ∀ v : Magma.tupS6A,
    ¬ @Equation1498 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1498) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1498) (by native_decide) v.1 v.2
    ((@Law1498.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1502 takes them (52 nodes). -/
def ordS6A_Law1502 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1502. -/
theorem noS6A_Law1502 : ∀ v : Magma.tupS6A,
    ¬ @Equation1502 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1502) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1502) (by native_decide) v.1 v.2
    ((@Law1502.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1506 takes them (62 nodes). -/
def ordS6A_Law1506 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1506. -/
theorem noS6A_Law1506 : ∀ v : Magma.tupS6A,
    ¬ @Equation1506 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1506) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1506) (by native_decide) v.1 v.2
    ((@Law1506.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1510 takes them (52 nodes). -/
def ordS6A_Law1510 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1510. -/
theorem noS6A_Law1510 : ∀ v : Magma.tupS6A,
    ¬ @Equation1510 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1510) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1510) (by native_decide) v.1 v.2
    ((@Law1510.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1518 takes them (343 nodes). -/
def ordS6A_Law1518 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1518. -/
theorem noS6A_Law1518 : ∀ v : Magma.tupS6A,
    ¬ @Equation1518 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1518) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law1518) (by native_decide) v.1 v.2
    ((@Law1518.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1521 takes them (195 nodes). -/
def ordS6A_Law1521 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1521. -/
theorem noS6A_Law1521 : ∀ v : Magma.tupS6A,
    ¬ @Equation1521 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1521) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1521) (by native_decide) v.1 v.2
    ((@Law1521.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1531 takes them (128 nodes). -/
def ordS6A_Law1531 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1531. -/
theorem noS6A_Law1531 : ∀ v : Magma.tupS6A,
    ¬ @Equation1531 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1531) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1531) (by native_decide) v.1 v.2
    ((@Law1531.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1535 takes them (253 nodes). -/
def ordS6A_Law1535 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1535. -/
theorem noS6A_Law1535 : ∀ v : Magma.tupS6A,
    ¬ @Equation1535 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1535) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1535) (by native_decide) v.1 v.2
    ((@Law1535.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1539 takes them (125 nodes). -/
def ordS6A_Law1539 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1539. -/
theorem noS6A_Law1539 : ∀ v : Magma.tupS6A,
    ¬ @Equation1539 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1539) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1539) (by native_decide) v.1 v.2
    ((@Law1539.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1547 takes them (123 nodes). -/
def ordS6A_Law1547 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1547. -/
theorem noS6A_Law1547 : ∀ v : Magma.tupS6A,
    ¬ @Equation1547 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1547) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1547) (by native_decide) v.1 v.2
    ((@Law1547.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1552 takes them (157 nodes). -/
def ordS6A_Law1552 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1552. -/
theorem noS6A_Law1552 : ∀ v : Magma.tupS6A,
    ¬ @Equation1552 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1552) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1552) (by native_decide) v.1 v.2
    ((@Law1552.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1556 takes them (93 nodes). -/
def ordS6A_Law1556 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1556. -/
theorem noS6A_Law1556 : ∀ v : Magma.tupS6A,
    ¬ @Equation1556 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1556) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1556) (by native_decide) v.1 v.2
    ((@Law1556.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1560 takes them (141 nodes). -/
def ordS6A_Law1560 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1560. -/
theorem noS6A_Law1560 : ∀ v : Magma.tupS6A,
    ¬ @Equation1560 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1560) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1560) (by native_decide) v.1 v.2
    ((@Law1560.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1564 takes them (87 nodes). -/
def ordS6A_Law1564 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1564. -/
theorem noS6A_Law1564 : ∀ v : Magma.tupS6A,
    ¬ @Equation1564 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1564) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1564) (by native_decide) v.1 v.2
    ((@Law1564.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1569 takes them (159 nodes). -/
def ordS6A_Law1569 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1569. -/
theorem noS6A_Law1569 : ∀ v : Magma.tupS6A,
    ¬ @Equation1569 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1569) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1569) (by native_decide) v.1 v.2
    ((@Law1569.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1573 takes them (37 nodes). -/
def ordS6A_Law1573 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1573. -/
theorem noS6A_Law1573 : ∀ v : Magma.tupS6A,
    ¬ @Equation1573 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1573) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1573) (by native_decide) v.1 v.2
    ((@Law1573.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1577 takes them (106 nodes). -/
def ordS6A_Law1577 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1577. -/
theorem noS6A_Law1577 : ∀ v : Magma.tupS6A,
    ¬ @Equation1577 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1577) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1577) (by native_decide) v.1 v.2
    ((@Law1577.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1581 takes them (37 nodes). -/
def ordS6A_Law1581 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1581. -/
theorem noS6A_Law1581 : ∀ v : Magma.tupS6A,
    ¬ @Equation1581 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1581) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1581) (by native_decide) v.1 v.2
    ((@Law1581.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1586 takes them (187 nodes). -/
def ordS6A_Law1586 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1586. -/
theorem noS6A_Law1586 : ∀ v : Magma.tupS6A,
    ¬ @Equation1586 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1586) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1586) (by native_decide) v.1 v.2
    ((@Law1586.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1590 takes them (95 nodes). -/
def ordS6A_Law1590 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1590. -/
theorem noS6A_Law1590 : ∀ v : Magma.tupS6A,
    ¬ @Equation1590 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1590) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1590) (by native_decide) v.1 v.2
    ((@Law1590.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1598 takes them (71 nodes). -/
def ordS6A_Law1598 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1598. -/
theorem noS6A_Law1598 : ∀ v : Magma.tupS6A,
    ¬ @Equation1598 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1598) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1598) (by native_decide) v.1 v.2
    ((@Law1598.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `23` equations. -/
theorem srch6A_refutes_13 :
    FamilyRefutes Magma.srch6A [
      1491, 1494, 1498, 1502, 1506, 1510, 1518, 1521, 1531, 1535, 1539, 1547, 1552, 1556, 1560,
      1564, 1569, 1573, 1577, 1581, 1586, 1590, 1598
    ] :=
  ⟨noS6A_Law1491, noS6A_Law1494, noS6A_Law1498, noS6A_Law1502, noS6A_Law1506, noS6A_Law1510, noS6A_Law1518, noS6A_Law1521, noS6A_Law1531, noS6A_Law1535, noS6A_Law1539, noS6A_Law1547, noS6A_Law1552, noS6A_Law1556, noS6A_Law1560, noS6A_Law1564, noS6A_Law1569, noS6A_Law1573, noS6A_Law1577, noS6A_Law1581, noS6A_Law1586, noS6A_Law1590, noS6A_Law1598⟩
