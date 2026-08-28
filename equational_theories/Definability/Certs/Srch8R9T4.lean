import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 5 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `13`
equations here, 3,222 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 265 takes them (741 nodes). -/
def ordS8R9_Law265 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 265. -/
theorem noS8R9_Law265 : ∀ v : Magma.tup8R9,
    ¬ @Equation265 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law265) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law265) (by native_decide) v.1 v.2
    ((@Law265.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 267 takes them (19 nodes). -/
def ordS8R9_Law267 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 267. -/
theorem noS8R9_Law267 : ∀ v : Magma.tup8R9,
    ¬ @Equation267 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law267) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law267) (by native_decide) v.1 v.2
    ((@Law267.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 268 takes them (741 nodes). -/
def ordS8R9_Law268 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 268. -/
theorem noS8R9_Law268 : ∀ v : Magma.tup8R9,
    ¬ @Equation268 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law268) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law268) (by native_decide) v.1 v.2
    ((@Law268.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 269 takes them (9 nodes). -/
def ordS8R9_Law269 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 269. -/
theorem noS8R9_Law269 : ∀ v : Magma.tup8R9,
    ¬ @Equation269 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law269) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law269) (by native_decide) v.1 v.2
    ((@Law269.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 276 takes them (64 nodes). -/
def ordS8R9_Law276 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 276. -/
theorem noS8R9_Law276 : ∀ v : Magma.tup8R9,
    ¬ @Equation276 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law276) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law276) (by native_decide) v.1 v.2
    ((@Law276.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 286 takes them (9 nodes). -/
def ordS8R9_Law286 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 286. -/
theorem noS8R9_Law286 : ∀ v : Magma.tup8R9,
    ¬ @Equation286 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law286) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law286) (by native_decide) v.1 v.2
    ((@Law286.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 294 takes them (741 nodes). -/
def ordS8R9_Law294 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 294. -/
theorem noS8R9_Law294 : ∀ v : Magma.tup8R9,
    ¬ @Equation294 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law294) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law294) (by native_decide) v.1 v.2
    ((@Law294.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 298 takes them (741 nodes). -/
def ordS8R9_Law298 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 298. -/
theorem noS8R9_Law298 : ∀ v : Magma.tup8R9,
    ¬ @Equation298 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law298) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law298) (by native_decide) v.1 v.2
    ((@Law298.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 302 takes them (9 nodes). -/
def ordS8R9_Law302 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 302. -/
theorem noS8R9_Law302 : ∀ v : Magma.tup8R9,
    ¬ @Equation302 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law302) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law302) (by native_decide) v.1 v.2
    ((@Law302.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 310 takes them (65 nodes). -/
def ordS8R9_Law310 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 310. -/
theorem noS8R9_Law310 : ∀ v : Magma.tup8R9,
    ¬ @Equation310 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law310) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law310) (by native_decide) v.1 v.2
    ((@Law310.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 311 takes them (65 nodes). -/
def ordS8R9_Law311 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 311. -/
theorem noS8R9_Law311 : ∀ v : Magma.tup8R9,
    ¬ @Equation311 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law311) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law311) (by native_decide) v.1 v.2
    ((@Law311.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 312 takes them (9 nodes). -/
def ordS8R9_Law312 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 312. -/
theorem noS8R9_Law312 : ∀ v : Magma.tup8R9,
    ¬ @Equation312 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law312) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law312) (by native_decide) v.1 v.2
    ((@Law312.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 318 takes them (9 nodes). -/
def ordS8R9_Law318 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 318. -/
theorem noS8R9_Law318 : ∀ v : Magma.tup8R9,
    ¬ @Equation318 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law318) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law318) (by native_decide) v.1 v.2
    ((@Law318.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch8R9_refutes_4 :
    FamilyRefutes Magma.srch8R9 [
      265, 267, 268, 269, 276, 286, 294, 298, 302, 310, 311, 312, 318
    ] :=
  ⟨noS8R9_Law265, noS8R9_Law267, noS8R9_Law268, noS8R9_Law269, noS8R9_Law276, noS8R9_Law286, noS8R9_Law294, noS8R9_Law298, noS8R9_Law302, noS8R9_Law310, noS8R9_Law311, noS8R9_Law312, noS8R9_Law318⟩
