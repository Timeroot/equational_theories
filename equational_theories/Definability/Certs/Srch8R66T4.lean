import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 5 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,511 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2043 takes them (1105 nodes). -/
def ordS8R66_Law2043 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2043. -/
theorem noS8R66_Law2043 : ∀ v : Magma.tup8R66,
    ¬ @Equation2043 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2043) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2043) (by native_decide) v.1 v.2
    ((@Law2043.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (271 nodes). -/
def ordS8R66_Law2051 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2051. -/
theorem noS8R66_Law2051 : ∀ v : Magma.tup8R66,
    ¬ @Equation2051 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (560 nodes). -/
def ordS8R66_Law2053 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2053. -/
theorem noS8R66_Law2053 : ∀ v : Magma.tup8R66,
    ¬ @Equation2053 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2060 takes them (1401 nodes). -/
def ordS8R66_Law2060 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2060. -/
theorem noS8R66_Law2060 : ∀ v : Magma.tup8R66,
    ¬ @Equation2060 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2060) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2060) (by native_decide) v.1 v.2
    ((@Law2060.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (95 nodes). -/
def ordS8R66_Law2064 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2064. -/
theorem noS8R66_Law2064 : ∀ v : Magma.tup8R66,
    ¬ @Equation2064 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2068 takes them (79 nodes). -/
def ordS8R66_Law2068 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2068. -/
theorem noS8R66_Law2068 : ∀ v : Magma.tup8R66,
    ¬ @Equation2068 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2068) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law2068) (by native_decide) v.1 v.2
    ((@Law2068.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R66_refutes_4 :
    FamilyRefutes Magma.srch8R66 [
      2043, 2051, 2053, 2060, 2064, 2068
    ] :=
  ⟨noS8R66_Law2043, noS8R66_Law2051, noS8R66_Law2053, noS8R66_Law2060, noS8R66_Law2064, noS8R66_Law2068⟩
