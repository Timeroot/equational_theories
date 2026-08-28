import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 8 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `10` equations here, 3,328 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1455 takes them (601 nodes). -/
def ordS8R52_Law1455 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1455. -/
theorem noS8R52_Law1455 : ∀ v : Magma.tup8R52,
    ¬ @Equation1455 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1456 takes them (233 nodes). -/
def ordS8R52_Law1456 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1456. -/
theorem noS8R52_Law1456 : ∀ v : Magma.tup8R52,
    ¬ @Equation1456 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1456) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1456) (by native_decide) v.1 v.2
    ((@Law1456.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1457 takes them (239 nodes). -/
def ordS8R52_Law1457 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1457. -/
theorem noS8R52_Law1457 : ∀ v : Magma.tup8R52,
    ¬ @Equation1457 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1457) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1457) (by native_decide) v.1 v.2
    ((@Law1457.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1458 takes them (241 nodes). -/
def ordS8R52_Law1458 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1458. -/
theorem noS8R52_Law1458 : ∀ v : Magma.tup8R52,
    ¬ @Equation1458 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1458) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1458) (by native_decide) v.1 v.2
    ((@Law1458.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1459 takes them (249 nodes). -/
def ordS8R52_Law1459 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1459. -/
theorem noS8R52_Law1459 : ∀ v : Magma.tup8R52,
    ¬ @Equation1459 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1459) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1459) (by native_decide) v.1 v.2
    ((@Law1459.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1460 takes them (201 nodes). -/
def ordS8R52_Law1460 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1460. -/
theorem noS8R52_Law1460 : ∀ v : Magma.tup8R52,
    ¬ @Equation1460 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1460) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law1460) (by native_decide) v.1 v.2
    ((@Law1460.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1478 takes them (406 nodes). -/
def ordS8R52_Law1478 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1478. -/
theorem noS8R52_Law1478 : ∀ v : Magma.tup8R52,
    ¬ @Equation1478 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1478) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1478) (by native_decide) v.1 v.2
    ((@Law1478.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1731 takes them (369 nodes). -/
def ordS8R52_Law1731 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1731. -/
theorem noS8R52_Law1731 : ∀ v : Magma.tup8R52,
    ¬ @Equation1731 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1731) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1731) (by native_decide) v.1 v.2
    ((@Law1731.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1861 takes them (393 nodes). -/
def ordS8R52_Law1861 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1861. -/
theorem noS8R52_Law1861 : ∀ v : Magma.tup8R52,
    ¬ @Equation1861 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1861) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1861) (by native_decide) v.1 v.2
    ((@Law1861.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2036 takes them (396 nodes). -/
def ordS8R52_Law2036 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2036. -/
theorem noS8R52_Law2036 : ∀ v : Magma.tup8R52,
    ¬ @Equation2036 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2036) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2036) (by native_decide) v.1 v.2
    ((@Law2036.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch8R52_refutes_7 :
    FamilyRefutes Magma.srch8R52 [
      1455, 1456, 1457, 1458, 1459, 1460, 1478, 1731, 1861, 2036
    ] :=
  ⟨noS8R52_Law1455, noS8R52_Law1456, noS8R52_Law1457, noS8R52_Law1458, noS8R52_Law1459, noS8R52_Law1460, noS8R52_Law1478, noS8R52_Law1731, noS8R52_Law1861, noS8R52_Law2036⟩
