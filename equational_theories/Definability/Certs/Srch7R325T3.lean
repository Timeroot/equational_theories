import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 4 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 1,762 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4129 takes them (406 nodes). -/
def ordS7R325_Law4129 : List (Fin 9) := [7, 8, 0, 3, 4, 1, 5, 2, 6]

/-- No member of the class satisfies equation 4129. -/
theorem noS7R325_Law4129 : ∀ v : Magma.tup7R325,
    ¬ @Equation4129 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4129) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4129) (by native_decide) v.1 v.2
    ((@Law4129.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4132 takes them (241 nodes). -/
def ordS7R325_Law4132 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4132. -/
theorem noS7R325_Law4132 : ∀ v : Magma.tup7R325,
    ¬ @Equation4132 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4132) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4132) (by native_decide) v.1 v.2
    ((@Law4132.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4133 takes them (66 nodes). -/
def ordS7R325_Law4133 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4133. -/
theorem noS7R325_Law4133 : ∀ v : Magma.tup7R325,
    ¬ @Equation4133 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4133) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4133) (by native_decide) v.1 v.2
    ((@Law4133.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4134 takes them (86 nodes). -/
def ordS7R325_Law4134 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4134. -/
theorem noS7R325_Law4134 : ∀ v : Magma.tup7R325,
    ¬ @Equation4134 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4134) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4134) (by native_decide) v.1 v.2
    ((@Law4134.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4136 takes them (38 nodes). -/
def ordS7R325_Law4136 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4136. -/
theorem noS7R325_Law4136 : ∀ v : Magma.tup7R325,
    ¬ @Equation4136 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4136) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4136) (by native_decide) v.1 v.2
    ((@Law4136.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (872 nodes). -/
def ordS7R325_Law4200 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4200. -/
theorem noS7R325_Law4200 : ∀ v : Magma.tup7R325,
    ¬ @Equation4200 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4229 takes them (53 nodes). -/
def ordS7R325_Law4229 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4229. -/
theorem noS7R325_Law4229 : ∀ v : Magma.tup7R325,
    ¬ @Equation4229 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4229) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4229) (by native_decide) v.1 v.2
    ((@Law4229.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch7R325_refutes_3 :
    FamilyRefutes Magma.srch7R325 [
      4129, 4132, 4133, 4134, 4136, 4200, 4229
    ] :=
  ⟨noS7R325_Law4129, noS7R325_Law4132, noS7R325_Law4133, noS7R325_Law4134, noS7R325_Law4136, noS7R325_Law4200, noS7R325_Law4229⟩
