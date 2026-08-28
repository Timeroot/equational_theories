import equational_theories.Definability.Srch_S8R24

/-!
# Structural certificate targets: `Magma.srch8R24`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R24_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 1,751 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R24_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 562 takes them (277 nodes). -/
def ordS8R24_Law562 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 562. -/
theorem noS8R24_Law562 : ∀ v : Magma.tup8R24,
    ¬ @Equation562 (Fin 8) (Magma.srch8R24 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S8R24.E) (tr := S8R24.tr) (z := S8R24.z)
    (st := S8R24.st) (X := S8R24.X) (envs := Magma.envsRed 8 S8R24.E 3)
    (ord := ordS8R24_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 8) (Magma.srch8R24 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (406 nodes). -/
def ordS8R24_Law3091 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3091. -/
theorem noS8R24_Law3091 : ∀ v : Magma.tup8R24,
    ¬ @Equation3091 (Fin 8) (Magma.srch8R24 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S8R24.E) (tr := S8R24.tr) (z := S8R24.z)
    (st := S8R24.st) (X := S8R24.X) (envs := Magma.envsRed 8 S8R24.E 3)
    (ord := ordS8R24_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 8) (Magma.srch8R24 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3588 takes them (537 nodes). -/
def ordS8R24_Law3588 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3588. -/
theorem noS8R24_Law3588 : ∀ v : Magma.tup8R24,
    ¬ @Equation3588 (Fin 8) (Magma.srch8R24 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3588) (E := S8R24.E) (tr := S8R24.tr) (z := S8R24.z)
    (st := S8R24.st) (X := S8R24.X) (envs := Magma.envsRed 8 S8R24.E 3)
    (ord := ordS8R24_Law3588) (by native_decide) v.1 v.2
    ((@Law3588.models_iff (Fin 8) (Magma.srch8R24 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3994 takes them (531 nodes). -/
def ordS8R24_Law3994 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3994. -/
theorem noS8R24_Law3994 : ∀ v : Magma.tup8R24,
    ¬ @Equation3994 (Fin 8) (Magma.srch8R24 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3994) (E := S8R24.E) (tr := S8R24.tr) (z := S8R24.z)
    (st := S8R24.st) (X := S8R24.X) (envs := Magma.envsRed 8 S8R24.E 3)
    (ord := ordS8R24_Law3994) (by native_decide) v.1 v.2
    ((@Law3994.models_iff (Fin 8) (Magma.srch8R24 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R24_refutes_0 :
    FamilyRefutes Magma.srch8R24 [
      562, 3091, 3588, 3994
    ] :=
  ⟨noS8R24_Law562, noS8R24_Law3091, noS8R24_Law3588, noS8R24_Law3994⟩
