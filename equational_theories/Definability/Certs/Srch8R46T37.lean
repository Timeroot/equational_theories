import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 38 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,667 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3997 takes them (732 nodes). -/
def ordS8R46_Law3997 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3997. -/
theorem noS8R46_Law3997 : ∀ v : Magma.tup8R46,
    ¬ @Equation3997 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4031 takes them (1935 nodes). -/
def ordS8R46_Law4031 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4031. -/
theorem noS8R46_Law4031 : ∀ v : Magma.tup8R46,
    ¬ @Equation4031 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4031) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law4031) (by native_decide) v.1 v.2
    ((@Law4031.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R46_refutes_37 :
    FamilyRefutes Magma.srch8R46 [
      3997, 4031
    ] :=
  ⟨noS8R46_Law3997, noS8R46_Law4031⟩
