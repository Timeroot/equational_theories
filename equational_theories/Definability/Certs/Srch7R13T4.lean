import equational_theories.Definability.Srch_S7R13

/-!
# Structural certificate targets: `Magma.srch7R13` (part 5 of 17)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,654 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1122 takes them (1936 nodes). -/
def ordS7R13_Law1122 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1122. -/
theorem noS7R13_Law1122 : ∀ v : Magma.tup7R13,
    ¬ @Equation1122 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (728 nodes). -/
def ordS7R13_Law1184 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1184. -/
theorem noS7R13_Law1184 : ∀ v : Magma.tup7R13,
    ¬ @Equation1184 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1525 takes them (337 nodes). -/
def ordS7R13_Law1525 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1525. -/
theorem noS7R13_Law1525 : ∀ v : Magma.tup7R13,
    ¬ @Equation1525 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1525) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law1525) (by native_decide) v.1 v.2
    ((@Law1525.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (653 nodes). -/
def ordS7R13_Law1635 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1635. -/
theorem noS7R13_Law1635 : ∀ v : Magma.tup7R13,
    ¬ @Equation1635 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch7R13_refutes_4 :
    FamilyRefutes Magma.srch7R13 [
      1122, 1184, 1525, 1635
    ] :=
  ⟨noS7R13_Law1122, noS7R13_Law1184, noS7R13_Law1525, noS7R13_Law1635⟩
