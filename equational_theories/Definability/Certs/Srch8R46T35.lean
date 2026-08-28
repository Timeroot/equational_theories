import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 36 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,538 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3890 takes them (2385 nodes). -/
def ordS8R46_Law3890 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3890. -/
theorem noS8R46_Law3890 : ∀ v : Magma.tup8R46,
    ¬ @Equation3890 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3890) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 2)
    (ord := ordS8R46_Law3890) (by native_decide) v.1 v.2
    ((@Law3890.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3939 takes them (436 nodes). -/
def ordS8R46_Law3939 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3939. -/
theorem noS8R46_Law3939 : ∀ v : Magma.tup8R46,
    ¬ @Equation3939 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3939) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law3939) (by native_decide) v.1 v.2
    ((@Law3939.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3943 takes them (401 nodes). -/
def ordS8R46_Law3943 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3943. -/
theorem noS8R46_Law3943 : ∀ v : Magma.tup8R46,
    ¬ @Equation3943 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3943) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law3943) (by native_decide) v.1 v.2
    ((@Law3943.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3947 takes them (316 nodes). -/
def ordS8R46_Law3947 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3947. -/
theorem noS8R46_Law3947 : ∀ v : Magma.tup8R46,
    ¬ @Equation3947 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3947) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 4)
    (ord := ordS8R46_Law3947) (by native_decide) v.1 v.2
    ((@Law3947.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R46_refutes_35 :
    FamilyRefutes Magma.srch8R46 [
      3890, 3939, 3943, 3947
    ] :=
  ⟨noS8R46_Law3890, noS8R46_Law3939, noS8R46_Law3943, noS8R46_Law3947⟩
