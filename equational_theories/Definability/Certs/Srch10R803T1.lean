import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 2 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 3,578 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 208 takes them (1041 nodes). -/
def ordS10R803_Law208 : List (Fin 8) := [3, 7, 6, 0, 1, 2, 4, 5]

/-- No member of the class satisfies equation 208. -/
theorem noS10R803_Law208 : ∀ v : Magma.tup10R803,
    ¬ @Equation208 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law208) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law208) (by native_decide) v.1 v.2
    ((@Law208.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 214 takes them (360 nodes). -/
def ordS10R803_Law214 : List (Fin 8) := [0, 7, 1, 3, 2, 4, 6, 5]

/-- No member of the class satisfies equation 214. -/
theorem noS10R803_Law214 : ∀ v : Magma.tup10R803,
    ¬ @Equation214 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law214) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law214) (by native_decide) v.1 v.2
    ((@Law214.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 242 takes them (183 nodes). -/
def ordS10R803_Law242 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 242. -/
theorem noS10R803_Law242 : ∀ v : Magma.tup10R803,
    ¬ @Equation242 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law242) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law242) (by native_decide) v.1 v.2
    ((@Law242.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 309 takes them (1291 nodes). -/
def ordS10R803_Law309 : List (Fin 8) := [6, 0, 3, 1, 7, 4, 2, 5]

/-- No member of the class satisfies equation 309. -/
theorem noS10R803_Law309 : ∀ v : Magma.tup10R803,
    ¬ @Equation309 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law309) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law309) (by native_decide) v.1 v.2
    ((@Law309.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 333 takes them (703 nodes). -/
def ordS10R803_Law333 : List (Fin 8) := [6, 3, 2, 7, 0, 5, 1, 4]

/-- No member of the class satisfies equation 333. -/
theorem noS10R803_Law333 : ∀ v : Magma.tup10R803,
    ¬ @Equation333 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law333) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law333) (by native_decide) v.1 v.2
    ((@Law333.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch10R803_refutes_1 :
    FamilyRefutes Magma.srch10R803 [
      208, 214, 242, 309, 333
    ] :=
  ⟨noS10R803_Law208, noS10R803_Law214, noS10R803_Law242, noS10R803_Law309, noS10R803_Law333⟩
