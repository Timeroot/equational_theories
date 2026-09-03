import equational_theories.Definability.Srch_S9R703

/-!
# Structural certificate targets: `Magma.srch9R703`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R703_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 1,466 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R703_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 427 takes them (248 nodes). -/
def ordS9R703_Law427 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 427. -/
theorem noS9R703_Law427 : ∀ v : Magma.tup9R703,
    ¬ @Equation427 (Fin 9) (Magma.srch9R703 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := S9R703.E) (tr := S9R703.tr) (z := S9R703.z)
    (st := S9R703.st) (X := S9R703.X) (envs := Magma.envsRed 9 S9R703.E 2)
    (ord := ordS9R703_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 9) (Magma.srch9R703 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 436 takes them (224 nodes). -/
def ordS9R703_Law436 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 436. -/
theorem noS9R703_Law436 : ∀ v : Magma.tup9R703,
    ¬ @Equation436 (Fin 9) (Magma.srch9R703 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law436) (E := S9R703.E) (tr := S9R703.tr) (z := S9R703.z)
    (st := S9R703.st) (X := S9R703.X) (envs := Magma.envsRed 9 S9R703.E 2)
    (ord := ordS9R703_Law436) (by native_decide) v.1 v.2
    ((@Law436.models_iff (Fin 9) (Magma.srch9R703 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 845 takes them (261 nodes). -/
def ordS9R703_Law845 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 845. -/
theorem noS9R703_Law845 : ∀ v : Magma.tup9R703,
    ¬ @Equation845 (Fin 9) (Magma.srch9R703 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law845) (E := S9R703.E) (tr := S9R703.tr) (z := S9R703.z)
    (st := S9R703.st) (X := S9R703.X) (envs := Magma.envsRed 9 S9R703.E 2)
    (ord := ordS9R703_Law845) (by native_decide) v.1 v.2
    ((@Law845.models_iff (Fin 9) (Magma.srch9R703 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2672 takes them (261 nodes). -/
def ordS9R703_Law2672 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2672. -/
theorem noS9R703_Law2672 : ∀ v : Magma.tup9R703,
    ¬ @Equation2672 (Fin 9) (Magma.srch9R703 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2672) (E := S9R703.E) (tr := S9R703.tr) (z := S9R703.z)
    (st := S9R703.st) (X := S9R703.X) (envs := Magma.envsRed 9 S9R703.E 2)
    (ord := ordS9R703_Law2672) (by native_decide) v.1 v.2
    ((@Law2672.models_iff (Fin 9) (Magma.srch9R703 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3058 takes them (224 nodes). -/
def ordS9R703_Law3058 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3058. -/
theorem noS9R703_Law3058 : ∀ v : Magma.tup9R703,
    ¬ @Equation3058 (Fin 9) (Magma.srch9R703 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3058) (E := S9R703.E) (tr := S9R703.tr) (z := S9R703.z)
    (st := S9R703.st) (X := S9R703.X) (envs := Magma.envsRed 9 S9R703.E 2)
    (ord := ordS9R703_Law3058) (by native_decide) v.1 v.2
    ((@Law3058.models_iff (Fin 9) (Magma.srch9R703 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (248 nodes). -/
def ordS9R703_Law3105 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3105. -/
theorem noS9R703_Law3105 : ∀ v : Magma.tup9R703,
    ¬ @Equation3105 (Fin 9) (Magma.srch9R703 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := S9R703.E) (tr := S9R703.tr) (z := S9R703.z)
    (st := S9R703.st) (X := S9R703.X) (envs := Magma.envsRed 9 S9R703.E 2)
    (ord := ordS9R703_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 9) (Magma.srch9R703 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch9R703_refutes_0 :
    FamilyRefutes Magma.srch9R703 [
      427, 436, 845, 2672, 3058, 3105
    ] :=
  ⟨noS9R703_Law427, noS9R703_Law436, noS9R703_Law845, noS9R703_Law2672, noS9R703_Law3058, noS9R703_Law3105⟩
