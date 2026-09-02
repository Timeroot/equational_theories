import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 8 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 3,533 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2269 takes them (451 nodes). -/
def ordS10R803_Law2269 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2269. -/
theorem noS10R803_Law2269 : ∀ v : Magma.tup10R803,
    ¬ @Equation2269 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2269) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2269) (by native_decide) v.1 v.2
    ((@Law2269.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2273 takes them (1098 nodes). -/
def ordS10R803_Law2273 : List (Fin 8) := [3, 0, 1, 7, 6, 5, 4, 2]

/-- No member of the class satisfies equation 2273. -/
theorem noS10R803_Law2273 : ∀ v : Magma.tup10R803,
    ¬ @Equation2273 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2273) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2273) (by native_decide) v.1 v.2
    ((@Law2273.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2277 takes them (582 nodes). -/
def ordS10R803_Law2277 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2277. -/
theorem noS10R803_Law2277 : ∀ v : Magma.tup10R803,
    ¬ @Equation2277 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2277) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2277) (by native_decide) v.1 v.2
    ((@Law2277.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2285 takes them (407 nodes). -/
def ordS10R803_Law2285 : List (Fin 8) := [1, 6, 4, 0, 2, 7, 5, 3]

/-- No member of the class satisfies equation 2285. -/
theorem noS10R803_Law2285 : ∀ v : Magma.tup10R803,
    ¬ @Equation2285 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2285) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law2285) (by native_decide) v.1 v.2
    ((@Law2285.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2310 takes them (362 nodes). -/
def ordS10R803_Law2310 : List (Fin 8) := [0, 3, 2, 1, 5, 6, 7, 4]

/-- No member of the class satisfies equation 2310. -/
theorem noS10R803_Law2310 : ∀ v : Magma.tup10R803,
    ¬ @Equation2310 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2310) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2310) (by native_decide) v.1 v.2
    ((@Law2310.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2314 takes them (177 nodes). -/
def ordS10R803_Law2314 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2314. -/
theorem noS10R803_Law2314 : ∀ v : Magma.tup10R803,
    ¬ @Equation2314 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2314) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2314) (by native_decide) v.1 v.2
    ((@Law2314.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2368 takes them (195 nodes). -/
def ordS10R803_Law2368 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2368. -/
theorem noS10R803_Law2368 : ∀ v : Magma.tup10R803,
    ¬ @Equation2368 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2368) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2368) (by native_decide) v.1 v.2
    ((@Law2368.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2420 takes them (78 nodes). -/
def ordS10R803_Law2420 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2420. -/
theorem noS10R803_Law2420 : ∀ v : Magma.tup10R803,
    ¬ @Equation2420 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2420) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law2420) (by native_decide) v.1 v.2
    ((@Law2420.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2425 takes them (183 nodes). -/
def ordS10R803_Law2425 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2425. -/
theorem noS10R803_Law2425 : ∀ v : Magma.tup10R803,
    ¬ @Equation2425 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2425) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law2425) (by native_decide) v.1 v.2
    ((@Law2425.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch10R803_refutes_7 :
    FamilyRefutes Magma.srch10R803 [
      2269, 2273, 2277, 2285, 2310, 2314, 2368, 2420, 2425
    ] :=
  ⟨noS10R803_Law2269, noS10R803_Law2273, noS10R803_Law2277, noS10R803_Law2285, noS10R803_Law2310, noS10R803_Law2314, noS10R803_Law2368, noS10R803_Law2420, noS10R803_Law2425⟩
