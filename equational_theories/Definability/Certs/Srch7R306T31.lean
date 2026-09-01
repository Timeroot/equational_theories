import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 32 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,496 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3195 takes them (445 nodes). -/
def ordS7R306_Law3195 : List (Fin 7) := [4, 3, 1, 0, 2, 5, 6]

/-- No member of the class satisfies equation 3195. -/
theorem noS7R306_Law3195 : ∀ v : Magma.tup7R306,
    ¬ @Equation3195 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3195) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law3195) (by native_decide) v.1 v.2
    ((@Law3195.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3269 takes them (1466 nodes). -/
def ordS7R306_Law3269 : List (Fin 7) := [0, 4, 2, 1, 5, 6, 3]

/-- No member of the class satisfies equation 3269. -/
theorem noS7R306_Law3269 : ∀ v : Magma.tup7R306,
    ¬ @Equation3269 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3269) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law3269) (by native_decide) v.1 v.2
    ((@Law3269.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3272 takes them (532 nodes). -/
def ordS7R306_Law3272 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3272. -/
theorem noS7R306_Law3272 : ∀ v : Magma.tup7R306,
    ¬ @Equation3272 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3272) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law3272) (by native_decide) v.1 v.2
    ((@Law3272.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3472 takes them (424 nodes). -/
def ordS7R306_Law3472 : List (Fin 7) := [6, 0, 2, 1, 4, 5, 3]

/-- No member of the class satisfies equation 3472. -/
theorem noS7R306_Law3472 : ∀ v : Magma.tup7R306,
    ¬ @Equation3472 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3472) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law3472) (by native_decide) v.1 v.2
    ((@Law3472.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3588 takes them (447 nodes). -/
def ordS7R306_Law3588 : List (Fin 7) := [3, 0, 1, 4, 6, 2, 5]

/-- No member of the class satisfies equation 3588. -/
theorem noS7R306_Law3588 : ∀ v : Magma.tup7R306,
    ¬ @Equation3588 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3588) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law3588) (by native_decide) v.1 v.2
    ((@Law3588.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3678 takes them (91 nodes). -/
def ordS7R306_Law3678 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3678. -/
theorem noS7R306_Law3678 : ∀ v : Magma.tup7R306,
    ¬ @Equation3678 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3678) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law3678) (by native_decide) v.1 v.2
    ((@Law3678.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3685 takes them (91 nodes). -/
def ordS7R306_Law3685 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3685. -/
theorem noS7R306_Law3685 : ∀ v : Magma.tup7R306,
    ¬ @Equation3685 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3685) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law3685) (by native_decide) v.1 v.2
    ((@Law3685.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch7R306_refutes_31 :
    FamilyRefutes Magma.srch7R306 [
      3195, 3269, 3272, 3472, 3588, 3678, 3685
    ] :=
  ⟨noS7R306_Law3195, noS7R306_Law3269, noS7R306_Law3272, noS7R306_Law3472, noS7R306_Law3588, noS7R306_Law3678, noS7R306_Law3685⟩
