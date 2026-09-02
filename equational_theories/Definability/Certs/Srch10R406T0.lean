import equational_theories.Definability.Srch_S10R406

/-!
# Structural certificate targets: `Magma.srch10R406`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R406_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 271 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R406_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 439 takes them (42 nodes). -/
def ordS10R406_Law439 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 439. -/
theorem noS10R406_Law439 : ∀ v : Magma.tup10R406,
    ¬ @Equation439 (Fin 10) (Magma.srch10R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law439) (E := S10R406.E) (tr := S10R406.tr) (z := S10R406.z)
    (st := S10R406.st) (X := S10R406.X) (envs := Magma.envsRed 10 S10R406.E 2)
    (ord := ordS10R406_Law439) (by native_decide) v.1 v.2
    ((@Law439.models_iff (Fin 10) (Magma.srch10R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 443 takes them (20 nodes). -/
def ordS10R406_Law443 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 443. -/
theorem noS10R406_Law443 : ∀ v : Magma.tup10R406,
    ¬ @Equation443 (Fin 10) (Magma.srch10R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law443) (E := S10R406.E) (tr := S10R406.tr) (z := S10R406.z)
    (st := S10R406.st) (X := S10R406.X) (envs := Magma.envsRed 10 S10R406.E 3)
    (ord := ordS10R406_Law443) (by native_decide) v.1 v.2
    ((@Law443.models_iff (Fin 10) (Magma.srch10R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (74 nodes). -/
def ordS10R406_Law1654 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1654. -/
theorem noS10R406_Law1654 : ∀ v : Magma.tup10R406,
    ¬ @Equation1654 (Fin 10) (Magma.srch10R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S10R406.E) (tr := S10R406.tr) (z := S10R406.z)
    (st := S10R406.st) (X := S10R406.X) (envs := Magma.envsRed 10 S10R406.E 2)
    (ord := ordS10R406_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 10) (Magma.srch10R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (74 nodes). -/
def ordS10R406_Law1840 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1840. -/
theorem noS10R406_Law1840 : ∀ v : Magma.tup10R406,
    ¬ @Equation1840 (Fin 10) (Magma.srch10R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S10R406.E) (tr := S10R406.tr) (z := S10R406.z)
    (st := S10R406.st) (X := S10R406.X) (envs := Magma.envsRed 10 S10R406.E 2)
    (ord := ordS10R406_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 10) (Magma.srch10R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (42 nodes). -/
def ordS10R406_Law3078 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3078. -/
theorem noS10R406_Law3078 : ∀ v : Magma.tup10R406,
    ¬ @Equation3078 (Fin 10) (Magma.srch10R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S10R406.E) (tr := S10R406.tr) (z := S10R406.z)
    (st := S10R406.st) (X := S10R406.X) (envs := Magma.envsRed 10 S10R406.E 2)
    (ord := ordS10R406_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 10) (Magma.srch10R406 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3197 takes them (19 nodes). -/
def ordS10R406_Law3197 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3197. -/
theorem noS10R406_Law3197 : ∀ v : Magma.tup10R406,
    ¬ @Equation3197 (Fin 10) (Magma.srch10R406 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3197) (E := S10R406.E) (tr := S10R406.tr) (z := S10R406.z)
    (st := S10R406.st) (X := S10R406.X) (envs := Magma.envsRed 10 S10R406.E 3)
    (ord := ordS10R406_Law3197) (by native_decide) v.1 v.2
    ((@Law3197.models_iff (Fin 10) (Magma.srch10R406 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch10R406_refutes_0 :
    FamilyRefutes Magma.srch10R406 [
      439, 443, 1654, 1840, 3078, 3197
    ] :=
  ⟨noS10R406_Law439, noS10R406_Law443, noS10R406_Law1654, noS10R406_Law1840, noS10R406_Law3078, noS10R406_Law3197⟩
