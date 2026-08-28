import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 191 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `6`
equations here, 2,926 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3336 takes them (769 nodes). -/
def ordS8R9_Law3336 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3336. -/
theorem noS8R9_Law3336 : ∀ v : Magma.tup8R9,
    ¬ @Equation3336 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3336) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3336) (by native_decide) v.1 v.2
    ((@Law3336.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3337 takes them (69 nodes). -/
def ordS8R9_Law3337 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3337. -/
theorem noS8R9_Law3337 : ∀ v : Magma.tup8R9,
    ¬ @Equation3337 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3337) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3337) (by native_decide) v.1 v.2
    ((@Law3337.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3339 takes them (776 nodes). -/
def ordS8R9_Law3339 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3339. -/
theorem noS8R9_Law3339 : ∀ v : Magma.tup8R9,
    ¬ @Equation3339 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3339) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3339) (by native_decide) v.1 v.2
    ((@Law3339.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3340 takes them (65 nodes). -/
def ordS8R9_Law3340 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3340. -/
theorem noS8R9_Law3340 : ∀ v : Magma.tup8R9,
    ¬ @Equation3340 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3340) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3340) (by native_decide) v.1 v.2
    ((@Law3340.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3341 takes them (65 nodes). -/
def ordS8R9_Law3341 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3341. -/
theorem noS8R9_Law3341 : ∀ v : Magma.tup8R9,
    ¬ @Equation3341 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3341) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3341) (by native_decide) v.1 v.2
    ((@Law3341.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3349 takes them (1182 nodes). -/
def ordS8R9_Law3349 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3349. -/
theorem noS8R9_Law3349 : ∀ v : Magma.tup8R9,
    ¬ @Equation3349 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3349) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3349) (by native_decide) v.1 v.2
    ((@Law3349.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R9_refutes_190 :
    FamilyRefutes Magma.srch8R9 [
      3336, 3337, 3339, 3340, 3341, 3349
    ] :=
  ⟨noS8R9_Law3336, noS8R9_Law3337, noS8R9_Law3339, noS8R9_Law3340, noS8R9_Law3341, noS8R9_Law3349⟩
