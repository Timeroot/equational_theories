import equational_theories.Definability.Srch_S10R404

/-!
# Structural certificate targets: `Magma.srch10R404`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R404_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 20 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R404_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1233 takes them (5 nodes). -/
def ordS10R404_Law1233 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1233. -/
theorem noS10R404_Law1233 : ∀ v : Magma.tup10R404,
    ¬ @Equation1233 (Fin 10) (Magma.srch10R404 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1233) (E := S10R404.E) (tr := S10R404.tr) (z := S10R404.z)
    (st := S10R404.st) (X := S10R404.X) (envs := Magma.envsRed 10 S10R404.E 3)
    (ord := ordS10R404_Law1233) (by native_decide) v.1 v.2
    ((@Law1233.models_iff (Fin 10) (Magma.srch10R404 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1236 takes them (5 nodes). -/
def ordS10R404_Law1236 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1236. -/
theorem noS10R404_Law1236 : ∀ v : Magma.tup10R404,
    ¬ @Equation1236 (Fin 10) (Magma.srch10R404 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1236) (E := S10R404.E) (tr := S10R404.tr) (z := S10R404.z)
    (st := S10R404.st) (X := S10R404.X) (envs := Magma.envsRed 10 S10R404.E 3)
    (ord := ordS10R404_Law1236) (by native_decide) v.1 v.2
    ((@Law1236.models_iff (Fin 10) (Magma.srch10R404 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2347 takes them (5 nodes). -/
def ordS10R404_Law2347 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2347. -/
theorem noS10R404_Law2347 : ∀ v : Magma.tup10R404,
    ¬ @Equation2347 (Fin 10) (Magma.srch10R404 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2347) (E := S10R404.E) (tr := S10R404.tr) (z := S10R404.z)
    (st := S10R404.st) (X := S10R404.X) (envs := Magma.envsRed 10 S10R404.E 3)
    (ord := ordS10R404_Law2347) (by native_decide) v.1 v.2
    ((@Law2347.models_iff (Fin 10) (Magma.srch10R404 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2398 takes them (5 nodes). -/
def ordS10R404_Law2398 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2398. -/
theorem noS10R404_Law2398 : ∀ v : Magma.tup10R404,
    ¬ @Equation2398 (Fin 10) (Magma.srch10R404 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2398) (E := S10R404.E) (tr := S10R404.tr) (z := S10R404.z)
    (st := S10R404.st) (X := S10R404.X) (envs := Magma.envsRed 10 S10R404.E 3)
    (ord := ordS10R404_Law2398) (by native_decide) v.1 v.2
    ((@Law2398.models_iff (Fin 10) (Magma.srch10R404 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch10R404_refutes_0 :
    FamilyRefutes Magma.srch10R404 [
      1233, 1236, 2347, 2398
    ] :=
  ⟨noS10R404_Law1233, noS10R404_Law1236, noS10R404_Law2347, noS10R404_Law2398⟩
