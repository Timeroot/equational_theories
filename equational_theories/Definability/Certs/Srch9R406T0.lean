import equational_theories.Definability.Srch_S9R406

/-!
# Structural certificate targets: `Magma.srch9R406`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R406_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 1,254 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R406_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 55 takes them (187 nodes). -/
def ordS9R406_Law55 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 55. -/
theorem noS9R406_Law55 : ∀ v : Magma.tup9R406,
    ¬ @Equation55 (Fin 9) (Magma.srch9R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law55) (E := S9R406.E) (tr := S9R406.tr) (z := S9R406.z)
    (st := S9R406.st) (X := S9R406.X) (envs := Magma.envsRed 9 S9R406.E 2)
    (ord := ordS9R406_Law55) (by native_decide) v.1 v.2
    ((@Law55.models_iff (Fin 9) (Magma.srch9R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 263 takes them (187 nodes). -/
def ordS9R406_Law263 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 263. -/
theorem noS9R406_Law263 : ∀ v : Magma.tup9R406,
    ¬ @Equation263 (Fin 9) (Magma.srch9R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law263) (E := S9R406.E) (tr := S9R406.tr) (z := S9R406.z)
    (st := S9R406.st) (X := S9R406.X) (envs := Magma.envsRed 9 S9R406.E 2)
    (ord := ordS9R406_Law263) (by native_decide) v.1 v.2
    ((@Law263.models_iff (Fin 9) (Magma.srch9R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1229 takes them (273 nodes). -/
def ordS9R406_Law1229 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1229. -/
theorem noS9R406_Law1229 : ∀ v : Magma.tup9R406,
    ¬ @Equation1229 (Fin 9) (Magma.srch9R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1229) (E := S9R406.E) (tr := S9R406.tr) (z := S9R406.z)
    (st := S9R406.st) (X := S9R406.X) (envs := Magma.envsRed 9 S9R406.E 2)
    (ord := ordS9R406_Law1229) (by native_decide) v.1 v.2
    ((@Law1229.models_iff (Fin 9) (Magma.srch9R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (167 nodes). -/
def ordS9R406_Law1635 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1635. -/
theorem noS9R406_Law1635 : ∀ v : Magma.tup9R406,
    ¬ @Equation1635 (Fin 9) (Magma.srch9R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S9R406.E) (tr := S9R406.tr) (z := S9R406.z)
    (st := S9R406.st) (X := S9R406.X) (envs := Magma.envsRed 9 S9R406.E 2)
    (ord := ordS9R406_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 9) (Magma.srch9R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (167 nodes). -/
def ordS9R406_Law1894 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1894. -/
theorem noS9R406_Law1894 : ∀ v : Magma.tup9R406,
    ¬ @Equation1894 (Fin 9) (Magma.srch9R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S9R406.E) (tr := S9R406.tr) (z := S9R406.z)
    (st := S9R406.st) (X := S9R406.X) (envs := Magma.envsRed 9 S9R406.E 2)
    (ord := ordS9R406_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 9) (Magma.srch9R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2300 takes them (273 nodes). -/
def ordS9R406_Law2300 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2300. -/
theorem noS9R406_Law2300 : ∀ v : Magma.tup9R406,
    ¬ @Equation2300 (Fin 9) (Magma.srch9R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2300) (E := S9R406.E) (tr := S9R406.tr) (z := S9R406.z)
    (st := S9R406.st) (X := S9R406.X) (envs := Magma.envsRed 9 S9R406.E 2)
    (ord := ordS9R406_Law2300) (by native_decide) v.1 v.2
    ((@Law2300.models_iff (Fin 9) (Magma.srch9R406 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch9R406_refutes_0 :
    FamilyRefutes Magma.srch9R406 [
      55, 263, 1229, 1635, 1894, 2300
    ] :=
  ⟨noS9R406_Law55, noS9R406_Law263, noS9R406_Law1229, noS9R406_Law1635, noS9R406_Law1894, noS9R406_Law2300⟩
