import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 17 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 3,361 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1657 takes them (1281 nodes). -/
def ordS7R12_Law1657 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1657. -/
theorem noS7R12_Law1657 : ∀ v : Magma.tup7R12,
    ¬ @Equation1657 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1657) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1657) (by native_decide) v.1 v.2
    ((@Law1657.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (855 nodes). -/
def ordS7R12_Law1658 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1658. -/
theorem noS7R12_Law1658 : ∀ v : Magma.tup7R12,
    ¬ @Equation1658 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (389 nodes). -/
def ordS7R12_Law1662 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1662. -/
theorem noS7R12_Law1662 : ∀ v : Magma.tup7R12,
    ¬ @Equation1662 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1664 takes them (179 nodes). -/
def ordS7R12_Law1664 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1664. -/
theorem noS7R12_Law1664 : ∀ v : Magma.tup7R12,
    ¬ @Equation1664 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1664) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1664) (by native_decide) v.1 v.2
    ((@Law1664.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1672 takes them (657 nodes). -/
def ordS7R12_Law1672 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1672. -/
theorem noS7R12_Law1672 : ∀ v : Magma.tup7R12,
    ¬ @Equation1672 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1672) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1672) (by native_decide) v.1 v.2
    ((@Law1672.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch7R12_refutes_16 :
    FamilyRefutes Magma.srch7R12 [
      1657, 1658, 1662, 1664, 1672
    ] :=
  ⟨noS7R12_Law1657, noS7R12_Law1658, noS7R12_Law1662, noS7R12_Law1664, noS7R12_Law1672⟩
