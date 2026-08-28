import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 6 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,267 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2090 takes them (228 nodes). -/
def ordS8R66_Law2090 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2090. -/
theorem noS8R66_Law2090 : ∀ v : Magma.tup8R66,
    ¬ @Equation2090 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (216 nodes). -/
def ordS8R66_Law2137 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2137. -/
theorem noS8R66_Law2137 : ∀ v : Magma.tup8R66,
    ¬ @Equation2137 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2152 takes them (134 nodes). -/
def ordS8R66_Law2152 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2152. -/
theorem noS8R66_Law2152 : ∀ v : Magma.tup8R66,
    ¬ @Equation2152 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2152) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law2152) (by native_decide) v.1 v.2
    ((@Law2152.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2241 takes them (147 nodes). -/
def ordS8R66_Law2241 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2241. -/
theorem noS8R66_Law2241 : ∀ v : Magma.tup8R66,
    ¬ @Equation2241 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2241) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2241) (by native_decide) v.1 v.2
    ((@Law2241.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2254 takes them (375 nodes). -/
def ordS8R66_Law2254 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2254. -/
theorem noS8R66_Law2254 : ∀ v : Magma.tup8R66,
    ¬ @Equation2254 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (351 nodes). -/
def ordS8R66_Law2267 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2267. -/
theorem noS8R66_Law2267 : ∀ v : Magma.tup8R66,
    ¬ @Equation2267 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2282 takes them (223 nodes). -/
def ordS8R66_Law2282 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2282. -/
theorem noS8R66_Law2282 : ∀ v : Magma.tup8R66,
    ¬ @Equation2282 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2282) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law2282) (by native_decide) v.1 v.2
    ((@Law2282.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2444 takes them (369 nodes). -/
def ordS8R66_Law2444 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2444. -/
theorem noS8R66_Law2444 : ∀ v : Magma.tup8R66,
    ¬ @Equation2444 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2447 takes them (155 nodes). -/
def ordS8R66_Law2447 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2447. -/
theorem noS8R66_Law2447 : ∀ v : Magma.tup8R66,
    ¬ @Equation2447 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2447) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2447) (by native_decide) v.1 v.2
    ((@Law2447.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (337 nodes). -/
def ordS8R66_Law2457 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2457. -/
theorem noS8R66_Law2457 : ∀ v : Magma.tup8R66,
    ¬ @Equation2457 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (431 nodes). -/
def ordS8R66_Law2470 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2470. -/
theorem noS8R66_Law2470 : ∀ v : Magma.tup8R66,
    ¬ @Equation2470 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2485 takes them (301 nodes). -/
def ordS8R66_Law2485 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2485. -/
theorem noS8R66_Law2485 : ∀ v : Magma.tup8R66,
    ¬ @Equation2485 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch8R66_refutes_5 :
    FamilyRefutes Magma.srch8R66 [
      2090, 2137, 2152, 2241, 2254, 2267, 2282, 2444, 2447, 2457, 2470, 2485
    ] :=
  ⟨noS8R66_Law2090, noS8R66_Law2137, noS8R66_Law2152, noS8R66_Law2241, noS8R66_Law2254, noS8R66_Law2267, noS8R66_Law2282, noS8R66_Law2444, noS8R66_Law2447, noS8R66_Law2457, noS8R66_Law2470, noS8R66_Law2485⟩
