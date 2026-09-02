import equational_theories.Definability.Srch_S10R802

/-!
# Structural certificate targets: `Magma.srch10R802` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R802_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,558 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R802_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 669 takes them (399 nodes). -/
def ordS10R802_Law669 : List (Fin 8) := [1, 7, 4, 2, 0, 6, 5, 3]

/-- No member of the class satisfies equation 669. -/
theorem noS10R802_Law669 : ∀ v : Magma.tup10R802,
    ¬ @Equation669 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law669) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law669) (by native_decide) v.1 v.2
    ((@Law669.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (63 nodes). -/
def ordS10R802_Law1442 : List (Fin 8) := [7, 5, 0, 4, 2, 6, 1, 3]

/-- No member of the class satisfies equation 1442. -/
theorem noS10R802_Law1442 : ∀ v : Magma.tup10R802,
    ¬ @Equation1442 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (95 nodes). -/
def ordS10R802_Law1481 : List (Fin 8) := [1, 0, 7, 4, 6, 5, 3, 2]

/-- No member of the class satisfies equation 1481. -/
theorem noS10R802_Law1481 : ∀ v : Magma.tup10R802,
    ¬ @Equation1481 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (1295 nodes). -/
def ordS10R802_Law1654 : List (Fin 8) := [7, 4, 0, 6, 5, 3, 1, 2]

/-- No member of the class satisfies equation 1654. -/
theorem noS10R802_Law1654 : ∀ v : Magma.tup10R802,
    ¬ @Equation1654 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (1509 nodes). -/
def ordS10R802_Law1840 : List (Fin 8) := [7, 3, 4, 0, 6, 5, 1, 2]

/-- No member of the class satisfies equation 1840. -/
theorem noS10R802_Law1840 : ∀ v : Magma.tup10R802,
    ¬ @Equation1840 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (84 nodes). -/
def ordS10R802_Law2051 : List (Fin 8) := [7, 6, 4, 2, 5, 1, 3, 0]

/-- No member of the class satisfies equation 2051. -/
theorem noS10R802_Law2051 : ∀ v : Magma.tup10R802,
    ¬ @Equation2051 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (113 nodes). -/
def ordS10R802_Law2090 : List (Fin 8) := [5, 7, 3, 4, 0, 6, 2, 1]

/-- No member of the class satisfies equation 2090. -/
theorem noS10R802_Law2090 : ∀ v : Magma.tup10R802,
    ¬ @Equation2090 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch10R802_refutes_0 :
    FamilyRefutes Magma.srch10R802 [
      669, 1442, 1481, 1654, 1840, 2051, 2090
    ] :=
  ⟨noS10R802_Law669, noS10R802_Law1442, noS10R802_Law1481, noS10R802_Law1654, noS10R802_Law1840, noS10R802_Law2051, noS10R802_Law2090⟩
