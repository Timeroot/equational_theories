import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 57 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,816 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4593 takes them (2229 nodes). -/
def ordS8R46_Law4593 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4593. -/
theorem noS8R46_Law4593 : ∀ v : Magma.tup8R46,
    ¬ @Equation4593 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4593) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law4593) (by native_decide) v.1 v.2
    ((@Law4593.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4602 takes them (483 nodes). -/
def ordS8R46_Law4602 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4602. -/
theorem noS8R46_Law4602 : ∀ v : Magma.tup8R46,
    ¬ @Equation4602 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4602) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law4602) (by native_decide) v.1 v.2
    ((@Law4602.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4655 takes them (665 nodes). -/
def ordS8R46_Law4655 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4655. -/
theorem noS8R46_Law4655 : ∀ v : Magma.tup8R46,
    ¬ @Equation4655 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4655) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law4655) (by native_decide) v.1 v.2
    ((@Law4655.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4675 takes them (439 nodes). -/
def ordS8R46_Law4675 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4675. -/
theorem noS8R46_Law4675 : ∀ v : Magma.tup8R46,
    ¬ @Equation4675 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4675) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 4)
    (ord := ordS8R46_Law4675) (by native_decide) v.1 v.2
    ((@Law4675.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R46_refutes_56 :
    FamilyRefutes Magma.srch8R46 [
      4593, 4602, 4655, 4675
    ] :=
  ⟨noS8R46_Law4593, noS8R46_Law4602, noS8R46_Law4655, noS8R46_Law4675⟩
