import equational_theories.Definability.Srch_S10R808

/-!
# Structural certificate targets: `Magma.srch10R808`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R808_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `16` equations here, 456 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R808_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 419 takes them (43 nodes). -/
def ordS10R808_Law419 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 419. -/
theorem noS10R808_Law419 : ∀ v : Magma.tup10R808,
    ¬ @Equation419 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 617 takes them (18 nodes). -/
def ordS10R808_Law617 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 617. -/
theorem noS10R808_Law617 : ∀ v : Magma.tup10R808,
    ¬ @Equation617 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law617) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law617) (by native_decide) v.1 v.2
    ((@Law617.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1045 takes them (43 nodes). -/
def ordS10R808_Law1045 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1045. -/
theorem noS10R808_Law1045 : ∀ v : Magma.tup10R808,
    ¬ @Equation1045 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1226 takes them (22 nodes). -/
def ordS10R808_Law1226 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1226. -/
theorem noS10R808_Law1226 : ∀ v : Magma.tup10R808,
    ¬ @Equation1226 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1226) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1226) (by native_decide) v.1 v.2
    ((@Law1226.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1231 takes them (43 nodes). -/
def ordS10R808_Law1231 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1231. -/
theorem noS10R808_Law1231 : ∀ v : Magma.tup10R808,
    ¬ @Equation1231 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1231) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1231) (by native_decide) v.1 v.2
    ((@Law1231.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (22 nodes). -/
def ordS10R808_Law1632 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1632. -/
theorem noS10R808_Law1632 : ∀ v : Magma.tup10R808,
    ¬ @Equation1632 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (15 nodes). -/
def ordS10R808_Law1691 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1691. -/
theorem noS10R808_Law1691 : ∀ v : Magma.tup10R808,
    ¬ @Equation1691 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1838 takes them (18 nodes). -/
def ordS10R808_Law1838 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1838. -/
theorem noS10R808_Law1838 : ∀ v : Magma.tup10R808,
    ¬ @Equation1838 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1838) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1838) (by native_decide) v.1 v.2
    ((@Law1838.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1921 takes them (22 nodes). -/
def ordS10R808_Law1921 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1921. -/
theorem noS10R808_Law1921 : ∀ v : Magma.tup10R808,
    ¬ @Equation1921 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1921) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law1921) (by native_decide) v.1 v.2
    ((@Law1921.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2263 takes them (43 nodes). -/
def ordS10R808_Law2263 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2263. -/
theorem noS10R808_Law2263 : ∀ v : Magma.tup10R808,
    ¬ @Equation2263 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2263) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law2263) (by native_decide) v.1 v.2
    ((@Law2263.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2327 takes them (22 nodes). -/
def ordS10R808_Law2327 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2327. -/
theorem noS10R808_Law2327 : ∀ v : Magma.tup10R808,
    ¬ @Equation2327 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2327) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law2327) (by native_decide) v.1 v.2
    ((@Law2327.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2449 takes them (43 nodes). -/
def ordS10R808_Law2449 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2449. -/
theorem noS10R808_Law2449 : ∀ v : Magma.tup10R808,
    ¬ @Equation2449 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2449) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law2449) (by native_decide) v.1 v.2
    ((@Law2449.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2936 takes them (15 nodes). -/
def ordS10R808_Law2936 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2936. -/
theorem noS10R808_Law2936 : ∀ v : Magma.tup10R808,
    ¬ @Equation2936 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2936) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law2936) (by native_decide) v.1 v.2
    ((@Law2936.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (43 nodes). -/
def ordS10R808_Law3075 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3075. -/
theorem noS10R808_Law3075 : ∀ v : Magma.tup10R808,
    ¬ @Equation3075 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3459 takes them (22 nodes). -/
def ordS10R808_Law3459 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3459. -/
theorem noS10R808_Law3459 : ∀ v : Magma.tup10R808,
    ¬ @Equation3459 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3459) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law3459) (by native_decide) v.1 v.2
    ((@Law3459.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3887 takes them (22 nodes). -/
def ordS10R808_Law3887 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3887. -/
theorem noS10R808_Law3887 : ∀ v : Magma.tup10R808,
    ¬ @Equation3887 (Fin 10) (Magma.srch10R808 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3887) (E := S10R808.E) (tr := S10R808.tr) (z := S10R808.z)
    (st := S10R808.st) (X := S10R808.X) (envs := Magma.envsRed 10 S10R808.E 2)
    (ord := ordS10R808_Law3887) (by native_decide) v.1 v.2
    ((@Law3887.models_iff (Fin 10) (Magma.srch10R808 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch10R808_refutes_0 :
    FamilyRefutes Magma.srch10R808 [
      419, 617, 1045, 1226, 1231, 1632, 1691, 1838, 1921, 2263, 2327, 2449, 2936, 3075, 3459, 3887
    ] :=
  ⟨noS10R808_Law419, noS10R808_Law617, noS10R808_Law1045, noS10R808_Law1226, noS10R808_Law1231, noS10R808_Law1632, noS10R808_Law1691, noS10R808_Law1838, noS10R808_Law1921, noS10R808_Law2263, noS10R808_Law2327, noS10R808_Law2449, noS10R808_Law2936, noS10R808_Law3075, noS10R808_Law3459, noS10R808_Law3887⟩
