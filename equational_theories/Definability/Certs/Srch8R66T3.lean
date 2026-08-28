import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 4 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,108 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1459 takes them (223 nodes). -/
def ordS8R66_Law1459 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1459. -/
theorem noS8R66_Law1459 : ∀ v : Magma.tup8R66,
    ¬ @Equation1459 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1459) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1459) (by native_decide) v.1 v.2
    ((@Law1459.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (289 nodes). -/
def ordS8R66_Law1481 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1481. -/
theorem noS8R66_Law1481 : ∀ v : Magma.tup8R66,
    ¬ @Equation1481 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (52 nodes). -/
def ordS8R66_Law1528 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1528. -/
theorem noS8R66_Law1528 : ∀ v : Magma.tup8R66,
    ¬ @Equation1528 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1543 takes them (45 nodes). -/
def ordS8R66_Law1543 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1543. -/
theorem noS8R66_Law1543 : ∀ v : Magma.tup8R66,
    ¬ @Equation1543 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1543) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1543) (by native_decide) v.1 v.2
    ((@Law1543.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1645 takes them (365 nodes). -/
def ordS8R66_Law1645 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1645. -/
theorem noS8R66_Law1645 : ∀ v : Magma.tup8R66,
    ¬ @Equation1645 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1645) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1645) (by native_decide) v.1 v.2
    ((@Law1645.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (431 nodes). -/
def ordS8R66_Law1658 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1658. -/
theorem noS8R66_Law1658 : ∀ v : Magma.tup8R66,
    ¬ @Equation1658 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (301 nodes). -/
def ordS8R66_Law1662 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1662. -/
theorem noS8R66_Law1662 : ∀ v : Magma.tup8R66,
    ¬ @Equation1662 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (198 nodes). -/
def ordS8R66_Law1780 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1780. -/
theorem noS8R66_Law1780 : ∀ v : Magma.tup8R66,
    ¬ @Equation1780 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (307 nodes). -/
def ordS8R66_Law1873 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1873. -/
theorem noS8R66_Law1873 : ∀ v : Magma.tup8R66,
    ¬ @Equation1873 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1887 takes them (433 nodes). -/
def ordS8R66_Law1887 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1887. -/
theorem noS8R66_Law1887 : ∀ v : Magma.tup8R66,
    ¬ @Equation1887 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1887) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1887) (by native_decide) v.1 v.2
    ((@Law1887.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (266 nodes). -/
def ordS8R66_Law1934 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1934. -/
theorem noS8R66_Law1934 : ∀ v : Magma.tup8R66,
    ¬ @Equation1934 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (198 nodes). -/
def ordS8R66_Law1949 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1949. -/
theorem noS8R66_Law1949 : ∀ v : Magma.tup8R66,
    ¬ @Equation1949 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch8R66_refutes_3 :
    FamilyRefutes Magma.srch8R66 [
      1459, 1481, 1528, 1543, 1645, 1658, 1662, 1780, 1873, 1887, 1934, 1949
    ] :=
  ⟨noS8R66_Law1459, noS8R66_Law1481, noS8R66_Law1528, noS8R66_Law1543, noS8R66_Law1645, noS8R66_Law1658, noS8R66_Law1662, noS8R66_Law1780, noS8R66_Law1873, noS8R66_Law1887, noS8R66_Law1934, noS8R66_Law1949⟩
