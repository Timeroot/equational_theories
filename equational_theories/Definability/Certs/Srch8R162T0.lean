import equational_theories.Definability.Srch_S8R162

/-!
# Structural certificate targets: `Magma.srch8R162`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R162_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 288 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R162_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 417 takes them (28 nodes). -/
def ordS8R162_Law417 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 417. -/
theorem noS8R162_Law417 : ∀ v : Magma.tup8R162,
    ¬ @Equation417 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (28 nodes). -/
def ordS8R162_Law620 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 620. -/
theorem noS8R162_Law620 : ∀ v : Magma.tup8R162,
    ¬ @Equation620 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 825 takes them (64 nodes). -/
def ordS8R162_Law825 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 825. -/
theorem noS8R162_Law825 : ∀ v : Magma.tup8R162,
    ¬ @Equation825 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law825) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law825) (by native_decide) v.1 v.2
    ((@Law825.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (28 nodes). -/
def ordS8R162_Law1023 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1023. -/
theorem noS8R162_Law1023 : ∀ v : Magma.tup8R162,
    ¬ @Equation1023 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (24 nodes). -/
def ordS8R162_Law2530 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2530. -/
theorem noS8R162_Law2530 : ∀ v : Magma.tup8R162,
    ¬ @Equation2530 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2669 takes them (64 nodes). -/
def ordS8R162_Law2669 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2669. -/
theorem noS8R162_Law2669 : ∀ v : Magma.tup8R162,
    ¬ @Equation2669 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2669) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law2669) (by native_decide) v.1 v.2
    ((@Law2669.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (28 nodes). -/
def ordS8R162_Law2909 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2909. -/
theorem noS8R162_Law2909 : ∀ v : Magma.tup8R162,
    ¬ @Equation2909 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (24 nodes). -/
def ordS8R162_Law3112 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3112. -/
theorem noS8R162_Law3112 : ∀ v : Magma.tup8R162,
    ¬ @Equation3112 (Fin 8) (Magma.srch8R162 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S8R162.E) (tr := S8R162.tr) (z := S8R162.z)
    (st := S8R162.st) (X := S8R162.X) (envs := Magma.envsRed 8 S8R162.E 2)
    (ord := ordS8R162_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 8) (Magma.srch8R162 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch8R162_refutes_0 :
    FamilyRefutes Magma.srch8R162 [
      417, 620, 825, 1023, 2530, 2669, 2909, 3112
    ] :=
  ⟨noS8R162_Law417, noS8R162_Law620, noS8R162_Law825, noS8R162_Law1023, noS8R162_Law2530, noS8R162_Law2669, noS8R162_Law2909, noS8R162_Law3112⟩
