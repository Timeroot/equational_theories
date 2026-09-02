import equational_theories.Definability.Srch_S10R807

/-!
# Structural certificate targets: `Magma.srch10R807`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R807_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 2,060 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R807_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 430 takes them (350 nodes). -/
def ordS10R807_Law430 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 430. -/
theorem noS10R807_Law430 : ∀ v : Magma.tup10R807,
    ¬ @Equation430 (Fin 10) (Magma.srch10R807 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S10R807.E) (tr := S10R807.tr) (z := S10R807.z)
    (st := S10R807.st) (X := S10R807.X) (envs := Magma.envsRed 10 S10R807.E 2)
    (ord := ordS10R807_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 10) (Magma.srch10R807 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1063 takes them (596 nodes). -/
def ordS10R807_Law1063 : List (Fin 9) := [3, 0, 8, 1, 5, 4, 7, 6, 2]

/-- No member of the class satisfies equation 1063. -/
theorem noS10R807_Law1063 : ∀ v : Magma.tup10R807,
    ¬ @Equation1063 (Fin 10) (Magma.srch10R807 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1063) (E := S10R807.E) (tr := S10R807.tr) (z := S10R807.z)
    (st := S10R807.st) (X := S10R807.X) (envs := Magma.envsRed 10 S10R807.E 3)
    (ord := ordS10R807_Law1063) (by native_decide) v.1 v.2
    ((@Law1063.models_iff (Fin 10) (Magma.srch10R807 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2472 takes them (752 nodes). -/
def ordS10R807_Law2472 : List (Fin 9) := [5, 7, 1, 0, 2, 3, 8, 6, 4]

/-- No member of the class satisfies equation 2472. -/
theorem noS10R807_Law2472 : ∀ v : Magma.tup10R807,
    ¬ @Equation2472 (Fin 10) (Magma.srch10R807 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2472) (E := S10R807.E) (tr := S10R807.tr) (z := S10R807.z)
    (st := S10R807.st) (X := S10R807.X) (envs := Magma.envsRed 10 S10R807.E 3)
    (ord := ordS10R807_Law2472) (by native_decide) v.1 v.2
    ((@Law2472.models_iff (Fin 10) (Magma.srch10R807 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (362 nodes). -/
def ordS10R807_Law3142 : List (Fin 9) := [8, 4, 7, 0, 1, 6, 3, 2, 5]

/-- No member of the class satisfies equation 3142. -/
theorem noS10R807_Law3142 : ∀ v : Magma.tup10R807,
    ¬ @Equation3142 (Fin 10) (Magma.srch10R807 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S10R807.E) (tr := S10R807.tr) (z := S10R807.z)
    (st := S10R807.st) (X := S10R807.X) (envs := Magma.envsRed 10 S10R807.E 2)
    (ord := ordS10R807_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 10) (Magma.srch10R807 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch10R807_refutes_0 :
    FamilyRefutes Magma.srch10R807 [
      430, 1063, 2472, 3142
    ] :=
  ⟨noS10R807_Law430, noS10R807_Law1063, noS10R807_Law2472, noS10R807_Law3142⟩
