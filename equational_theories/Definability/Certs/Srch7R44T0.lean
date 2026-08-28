import equational_theories.Definability.Srch_S7R44

/-!
# Structural certificate targets: `Magma.srch7R44`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R44_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 345 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R44_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1660 takes them (78 nodes). -/
def ordS7R44_Law1660 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1660. -/
theorem noS7R44_Law1660 : ∀ v : Magma.tup7R44,
    ¬ @Equation1660 (Fin 7) (Magma.srch7R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1660) (E := S7R44.E) (tr := S7R44.tr) (z := S7R44.z)
    (st := S7R44.st) (X := S7R44.X) (envs := Magma.envsRed 7 S7R44.E 3)
    (ord := ordS7R44_Law1660) (by native_decide) v.1 v.2
    ((@Law1660.models_iff (Fin 7) (Magma.srch7R44 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1668 takes them (80 nodes). -/
def ordS7R44_Law1668 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1668. -/
theorem noS7R44_Law1668 : ∀ v : Magma.tup7R44,
    ¬ @Equation1668 (Fin 7) (Magma.srch7R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1668) (E := S7R44.E) (tr := S7R44.tr) (z := S7R44.z)
    (st := S7R44.st) (X := S7R44.X) (envs := Magma.envsRed 7 S7R44.E 3)
    (ord := ordS7R44_Law1668) (by native_decide) v.1 v.2
    ((@Law1668.models_iff (Fin 7) (Magma.srch7R44 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1871 takes them (79 nodes). -/
def ordS7R44_Law1871 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1871. -/
theorem noS7R44_Law1871 : ∀ v : Magma.tup7R44,
    ¬ @Equation1871 (Fin 7) (Magma.srch7R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1871) (E := S7R44.E) (tr := S7R44.tr) (z := S7R44.z)
    (st := S7R44.st) (X := S7R44.X) (envs := Magma.envsRed 7 S7R44.E 3)
    (ord := ordS7R44_Law1871) (by native_decide) v.1 v.2
    ((@Law1871.models_iff (Fin 7) (Magma.srch7R44 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1875 takes them (82 nodes). -/
def ordS7R44_Law1875 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1875. -/
theorem noS7R44_Law1875 : ∀ v : Magma.tup7R44,
    ¬ @Equation1875 (Fin 7) (Magma.srch7R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1875) (E := S7R44.E) (tr := S7R44.tr) (z := S7R44.z)
    (st := S7R44.st) (X := S7R44.X) (envs := Magma.envsRed 7 S7R44.E 3)
    (ord := ordS7R44_Law1875) (by native_decide) v.1 v.2
    ((@Law1875.models_iff (Fin 7) (Magma.srch7R44 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4415 takes them (14 nodes). -/
def ordS7R44_Law4415 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4415. -/
theorem noS7R44_Law4415 : ∀ v : Magma.tup7R44,
    ¬ @Equation4415 (Fin 7) (Magma.srch7R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4415) (E := S7R44.E) (tr := S7R44.tr) (z := S7R44.z)
    (st := S7R44.st) (X := S7R44.X) (envs := Magma.envsRed 7 S7R44.E 3)
    (ord := ordS7R44_Law4415) (by native_decide) v.1 v.2
    ((@Law4415.models_iff (Fin 7) (Magma.srch7R44 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4430 takes them (12 nodes). -/
def ordS7R44_Law4430 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4430. -/
theorem noS7R44_Law4430 : ∀ v : Magma.tup7R44,
    ¬ @Equation4430 (Fin 7) (Magma.srch7R44 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4430) (E := S7R44.E) (tr := S7R44.tr) (z := S7R44.z)
    (st := S7R44.st) (X := S7R44.X) (envs := Magma.envsRed 7 S7R44.E 4)
    (ord := ordS7R44_Law4430) (by native_decide) v.1 v.2
    ((@Law4430.models_iff (Fin 7) (Magma.srch7R44 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R44_refutes_0 :
    FamilyRefutes Magma.srch7R44 [
      1660, 1668, 1871, 1875, 4415, 4430
    ] :=
  ⟨noS7R44_Law1660, noS7R44_Law1668, noS7R44_Law1871, noS7R44_Law1875, noS7R44_Law4415, noS7R44_Law4430⟩
