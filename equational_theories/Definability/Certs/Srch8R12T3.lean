import equational_theories.Definability.Srch_S8R12

/-!
# Structural certificate targets: `Magma.srch8R12` (part 4 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,829 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3091 takes them (2169 nodes). -/
def ordS8R12_Law3091 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3091. -/
theorem noS8R12_Law3091 : ∀ v : Magma.tup8R12,
    ¬ @Equation3091 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3388 takes them (645 nodes). -/
def ordS8R12_Law3388 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3388. -/
theorem noS8R12_Law3388 : ∀ v : Magma.tup8R12,
    ¬ @Equation3388 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3388) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law3388) (by native_decide) v.1 v.2
    ((@Law3388.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4143 takes them (1015 nodes). -/
def ordS8R12_Law4143 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4143. -/
theorem noS8R12_Law4143 : ∀ v : Magma.tup8R12,
    ¬ @Equation4143 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4143) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law4143) (by native_decide) v.1 v.2
    ((@Law4143.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R12_refutes_3 :
    FamilyRefutes Magma.srch8R12 [
      3091, 3388, 4143
    ] :=
  ⟨noS8R12_Law3091, noS8R12_Law3388, noS8R12_Law4143⟩
