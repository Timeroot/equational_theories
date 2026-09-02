import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 6 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 3,574 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1234 takes them (681 nodes). -/
def ordS10R803_Law1234 : List (Fin 8) := [6, 2, 0, 7, 1, 5, 3, 4]

/-- No member of the class satisfies equation 1234. -/
theorem noS10R803_Law1234 : ∀ v : Magma.tup10R803,
    ¬ @Equation1234 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1234) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1234) (by native_decide) v.1 v.2
    ((@Law1234.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1245 takes them (195 nodes). -/
def ordS10R803_Law1245 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1245. -/
theorem noS10R803_Law1245 : ∀ v : Magma.tup10R803,
    ¬ @Equation1245 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1245) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1245) (by native_decide) v.1 v.2
    ((@Law1245.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1259 takes them (177 nodes). -/
def ordS10R803_Law1259 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1259. -/
theorem noS10R803_Law1259 : ∀ v : Magma.tup10R803,
    ¬ @Equation1259 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1259) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1259) (by native_decide) v.1 v.2
    ((@Law1259.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1262 takes them (535 nodes). -/
def ordS10R803_Law1262 : List (Fin 8) := [2, 1, 7, 5, 0, 6, 3, 4]

/-- No member of the class satisfies equation 1262. -/
theorem noS10R803_Law1262 : ∀ v : Magma.tup10R803,
    ¬ @Equation1262 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1262) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1262) (by native_decide) v.1 v.2
    ((@Law1262.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1265 takes them (183 nodes). -/
def ordS10R803_Law1265 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1265. -/
theorem noS10R803_Law1265 : ∀ v : Magma.tup10R803,
    ¬ @Equation1265 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1265) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law1265) (by native_decide) v.1 v.2
    ((@Law1265.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1266 takes them (422 nodes). -/
def ordS10R803_Law1266 : List (Fin 8) := [7, 6, 2, 4, 1, 0, 5, 3]

/-- No member of the class satisfies equation 1266. -/
theorem noS10R803_Law1266 : ∀ v : Magma.tup10R803,
    ¬ @Equation1266 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1266) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1266) (by native_decide) v.1 v.2
    ((@Law1266.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1270 takes them (369 nodes). -/
def ordS10R803_Law1270 : List (Fin 8) := [1, 0, 3, 7, 2, 4, 6, 5]

/-- No member of the class satisfies equation 1270. -/
theorem noS10R803_Law1270 : ∀ v : Magma.tup10R803,
    ¬ @Equation1270 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1270) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law1270) (by native_decide) v.1 v.2
    ((@Law1270.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1271 takes them (81 nodes). -/
def ordS10R803_Law1271 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1271. -/
theorem noS10R803_Law1271 : ∀ v : Magma.tup10R803,
    ¬ @Equation1271 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1271) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law1271) (by native_decide) v.1 v.2
    ((@Law1271.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1631 takes them (931 nodes). -/
def ordS10R803_Law1631 : List (Fin 8) := [3, 0, 1, 6, 2, 5, 7, 4]

/-- No member of the class satisfies equation 1631. -/
theorem noS10R803_Law1631 : ∀ v : Magma.tup10R803,
    ¬ @Equation1631 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1631) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law1631) (by native_decide) v.1 v.2
    ((@Law1631.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch10R803_refutes_5 :
    FamilyRefutes Magma.srch10R803 [
      1234, 1245, 1259, 1262, 1265, 1266, 1270, 1271, 1631
    ] :=
  ⟨noS10R803_Law1234, noS10R803_Law1245, noS10R803_Law1259, noS10R803_Law1262, noS10R803_Law1265, noS10R803_Law1266, noS10R803_Law1270, noS10R803_Law1271, noS10R803_Law1631⟩
