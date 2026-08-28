import equational_theories.Definability.Srch_S8R41

/-!
# Structural certificate targets: `Magma.srch8R41` (part 4 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R41_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,311 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R41_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4143 takes them (835 nodes). -/
def ordS8R41_Law4143 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4143. -/
theorem noS8R41_Law4143 : ∀ v : Magma.tup8R41,
    ¬ @Equation4143 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4143) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law4143) (by native_decide) v.1 v.2
    ((@Law4143.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4209 takes them (833 nodes). -/
def ordS8R41_Law4209 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4209. -/
theorem noS8R41_Law4209 : ∀ v : Magma.tup8R41,
    ¬ @Equation4209 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4209) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law4209) (by native_decide) v.1 v.2
    ((@Law4209.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (643 nodes). -/
def ordS8R41_Law4243 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4243. -/
theorem noS8R41_Law4243 : ∀ v : Magma.tup8R41,
    ¬ @Equation4243 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 4)
    (ord := ordS8R41_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R41_refutes_3 :
    FamilyRefutes Magma.srch8R41 [
      4143, 4209, 4243
    ] :=
  ⟨noS8R41_Law4143, noS8R41_Law4209, noS8R41_Law4243⟩
