import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 1 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,051 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 10 takes them (439 nodes). -/
def ordS10R803_Law10 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 10. -/
theorem noS10R803_Law10 : ∀ v : Magma.tup10R803,
    ¬ @Equation10 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law10) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law10) (by native_decide) v.1 v.2
    ((@Law10.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 25 takes them (437 nodes). -/
def ordS10R803_Law25 : List (Fin 8) := [6, 2, 1, 3, 5, 7, 0, 4]

/-- No member of the class satisfies equation 25. -/
theorem noS10R803_Law25 : ∀ v : Magma.tup10R803,
    ¬ @Equation25 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law25) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law25) (by native_decide) v.1 v.2
    ((@Law25.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 101 takes them (1084 nodes). -/
def ordS10R803_Law101 : List (Fin 8) := [3, 7, 1, 6, 2, 0, 4, 5]

/-- No member of the class satisfies equation 101. -/
theorem noS10R803_Law101 : ∀ v : Magma.tup10R803,
    ¬ @Equation101 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law101) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law101) (by native_decide) v.1 v.2
    ((@Law101.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 110 takes them (435 nodes). -/
def ordS10R803_Law110 : List (Fin 8) := [5, 7, 2, 1, 6, 4, 0, 3]

/-- No member of the class satisfies equation 110. -/
theorem noS10R803_Law110 : ∀ v : Magma.tup10R803,
    ¬ @Equation110 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law110) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law110) (by native_decide) v.1 v.2
    ((@Law110.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 111 takes them (186 nodes). -/
def ordS10R803_Law111 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 111. -/
theorem noS10R803_Law111 : ∀ v : Magma.tup10R803,
    ¬ @Equation111 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law111) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law111) (by native_decide) v.1 v.2
    ((@Law111.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 153 takes them (235 nodes). -/
def ordS10R803_Law153 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 153. -/
theorem noS10R803_Law153 : ∀ v : Magma.tup10R803,
    ¬ @Equation153 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law153) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law153) (by native_decide) v.1 v.2
    ((@Law153.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 156 takes them (235 nodes). -/
def ordS10R803_Law156 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 156. -/
theorem noS10R803_Law156 : ∀ v : Magma.tup10R803,
    ¬ @Equation156 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law156) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law156) (by native_decide) v.1 v.2
    ((@Law156.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch10R803_refutes_0 :
    FamilyRefutes Magma.srch10R803 [
      10, 25, 101, 110, 111, 153, 156
    ] :=
  ⟨noS10R803_Law10, noS10R803_Law25, noS10R803_Law101, noS10R803_Law110, noS10R803_Law111, noS10R803_Law153, noS10R803_Law156⟩
