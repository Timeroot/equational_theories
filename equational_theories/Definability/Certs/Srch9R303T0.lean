import equational_theories.Definability.Srch_S9R303

/-!
# Structural certificate targets: `Magma.srch9R303`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R303_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 30 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R303_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1443 takes them (5 nodes). -/
def ordS9R303_Law1443 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1443. -/
theorem noS9R303_Law1443 : ∀ v : Magma.tup9R303,
    ¬ @Equation1443 (Fin 9) (Magma.srch9R303 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1443) (E := S9R303.E) (tr := S9R303.tr) (z := S9R303.z)
    (st := S9R303.st) (X := S9R303.X) (envs := Magma.envsRed 9 S9R303.E 3)
    (ord := ordS9R303_Law1443) (by native_decide) v.1 v.2
    ((@Law1443.models_iff (Fin 9) (Magma.srch9R303 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2093 takes them (5 nodes). -/
def ordS9R303_Law2093 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2093. -/
theorem noS9R303_Law2093 : ∀ v : Magma.tup9R303,
    ¬ @Equation2093 (Fin 9) (Magma.srch9R303 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2093) (E := S9R303.E) (tr := S9R303.tr) (z := S9R303.z)
    (st := S9R303.st) (X := S9R303.X) (envs := Magma.envsRed 9 S9R303.E 3)
    (ord := ordS9R303_Law2093) (by native_decide) v.1 v.2
    ((@Law2093.models_iff (Fin 9) (Magma.srch9R303 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (5 nodes). -/
def ordS9R303_Law3521 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3521. -/
theorem noS9R303_Law3521 : ∀ v : Magma.tup9R303,
    ¬ @Equation3521 (Fin 9) (Magma.srch9R303 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S9R303.E) (tr := S9R303.tr) (z := S9R303.z)
    (st := S9R303.st) (X := S9R303.X) (envs := Magma.envsRed 9 S9R303.E 2)
    (ord := ordS9R303_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 9) (Magma.srch9R303 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (5 nodes). -/
def ordS9R303_Law3952 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3952. -/
theorem noS9R303_Law3952 : ∀ v : Magma.tup9R303,
    ¬ @Equation3952 (Fin 9) (Magma.srch9R303 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S9R303.E) (tr := S9R303.tr) (z := S9R303.z)
    (st := S9R303.st) (X := S9R303.X) (envs := Magma.envsRed 9 S9R303.E 2)
    (ord := ordS9R303_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 9) (Magma.srch9R303 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4314 takes them (5 nodes). -/
def ordS9R303_Law4314 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4314. -/
theorem noS9R303_Law4314 : ∀ v : Magma.tup9R303,
    ¬ @Equation4314 (Fin 9) (Magma.srch9R303 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S9R303.E) (tr := S9R303.tr) (z := S9R303.z)
    (st := S9R303.st) (X := S9R303.X) (envs := Magma.envsRed 9 S9R303.E 2)
    (ord := ordS9R303_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 9) (Magma.srch9R303 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4606 takes them (5 nodes). -/
def ordS9R303_Law4606 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4606. -/
theorem noS9R303_Law4606 : ∀ v : Magma.tup9R303,
    ¬ @Equation4606 (Fin 9) (Magma.srch9R303 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4606) (E := S9R303.E) (tr := S9R303.tr) (z := S9R303.z)
    (st := S9R303.st) (X := S9R303.X) (envs := Magma.envsRed 9 S9R303.E 2)
    (ord := ordS9R303_Law4606) (by native_decide) v.1 v.2
    ((@Law4606.models_iff (Fin 9) (Magma.srch9R303 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch9R303_refutes_0 :
    FamilyRefutes Magma.srch9R303 [
      1443, 2093, 3521, 3952, 4314, 4606
    ] :=
  ⟨noS9R303_Law1443, noS9R303_Law2093, noS9R303_Law3521, noS9R303_Law3952, noS9R303_Law4314, noS9R303_Law4606⟩
