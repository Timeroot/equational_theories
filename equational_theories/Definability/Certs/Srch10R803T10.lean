import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 11 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 2,041 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3052 takes them (406 nodes). -/
def ordS10R803_Law3052 : List (Fin 8) := [1, 6, 0, 2, 7, 3, 4, 5]

/-- No member of the class satisfies equation 3052. -/
theorem noS10R803_Law3052 : ∀ v : Magma.tup10R803,
    ¬ @Equation3052 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3052) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3052) (by native_decide) v.1 v.2
    ((@Law3052.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3071 takes them (296 nodes). -/
def ordS10R803_Law3071 : List (Fin 8) := [1, 3, 2, 6, 0, 7, 5, 4]

/-- No member of the class satisfies equation 3071. -/
theorem noS10R803_Law3071 : ∀ v : Magma.tup10R803,
    ¬ @Equation3071 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3071) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3071) (by native_decide) v.1 v.2
    ((@Law3071.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (795 nodes). -/
def ordS10R803_Law3142 : List (Fin 8) := [7, 2, 1, 3, 5, 6, 0, 4]

/-- No member of the class satisfies equation 3142. -/
theorem noS10R803_Law3142 : ∀ v : Magma.tup10R803,
    ¬ @Equation3142 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3265 takes them (544 nodes). -/
def ordS10R803_Law3265 : List (Fin 8) := [3, 2, 5, 0, 6, 7, 4, 1]

/-- No member of the class satisfies equation 3265. -/
theorem noS10R803_Law3265 : ∀ v : Magma.tup10R803,
    ¬ @Equation3265 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3265) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3265) (by native_decide) v.1 v.2
    ((@Law3265.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch10R803_refutes_10 :
    FamilyRefutes Magma.srch10R803 [
      3052, 3071, 3142, 3265
    ] :=
  ⟨noS10R803_Law3052, noS10R803_Law3071, noS10R803_Law3142, noS10R803_Law3265⟩
