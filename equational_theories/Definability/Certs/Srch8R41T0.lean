import equational_theories.Definability.Srch_S8R41

/-!
# Structural certificate targets: `Magma.srch8R41` (part 1 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R41_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 3,415 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R41_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 327 takes them (605 nodes). -/
def ordS8R41_Law327 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 327. -/
theorem noS8R41_Law327 : ∀ v : Magma.tup8R41,
    ¬ @Equation327 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law327) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law327) (by native_decide) v.1 v.2
    ((@Law327.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 395 takes them (643 nodes). -/
def ordS8R41_Law395 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 395. -/
theorem noS8R41_Law395 : ∀ v : Magma.tup8R41,
    ¬ @Equation395 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law395) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law395) (by native_decide) v.1 v.2
    ((@Law395.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 562 takes them (669 nodes). -/
def ordS8R41_Law562 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 562. -/
theorem noS8R41_Law562 : ∀ v : Magma.tup8R41,
    ¬ @Equation562 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (715 nodes). -/
def ordS8R41_Law3091 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3091. -/
theorem noS8R41_Law3091 : ∀ v : Magma.tup8R41,
    ¬ @Equation3091 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3317 takes them (783 nodes). -/
def ordS8R41_Law3317 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3317. -/
theorem noS8R41_Law3317 : ∀ v : Magma.tup8R41,
    ¬ @Equation3317 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3317) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3317) (by native_decide) v.1 v.2
    ((@Law3317.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch8R41_refutes_0 :
    FamilyRefutes Magma.srch8R41 [
      327, 395, 562, 3091, 3317
    ] :=
  ⟨noS8R41_Law327, noS8R41_Law395, noS8R41_Law562, noS8R41_Law3091, noS8R41_Law3317⟩
