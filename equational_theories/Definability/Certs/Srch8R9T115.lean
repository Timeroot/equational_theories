import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 116 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `5`
equations here, 3,554 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2195 takes them (764 nodes). -/
def ordS8R9_Law2195 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2195. -/
theorem noS8R9_Law2195 : ∀ v : Magma.tup8R9,
    ¬ @Equation2195 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2195) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2195) (by native_decide) v.1 v.2
    ((@Law2195.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2199 takes them (1537 nodes). -/
def ordS8R9_Law2199 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2199. -/
theorem noS8R9_Law2199 : ∀ v : Magma.tup8R9,
    ¬ @Equation2199 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2199) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2199) (by native_decide) v.1 v.2
    ((@Law2199.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2207 takes them (764 nodes). -/
def ordS8R9_Law2207 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2207. -/
theorem noS8R9_Law2207 : ∀ v : Magma.tup8R9,
    ¬ @Equation2207 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2207) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2207) (by native_decide) v.1 v.2
    ((@Law2207.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2212 takes them (49 nodes). -/
def ordS8R9_Law2212 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2212. -/
theorem noS8R9_Law2212 : ∀ v : Magma.tup8R9,
    ¬ @Equation2212 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2212) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2212) (by native_decide) v.1 v.2
    ((@Law2212.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2217 takes them (440 nodes). -/
def ordS8R9_Law2217 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2217. -/
theorem noS8R9_Law2217 : ∀ v : Magma.tup8R9,
    ¬ @Equation2217 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2217) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2217) (by native_decide) v.1 v.2
    ((@Law2217.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch8R9_refutes_115 :
    FamilyRefutes Magma.srch8R9 [
      2195, 2199, 2207, 2212, 2217
    ] :=
  ⟨noS8R9_Law2195, noS8R9_Law2199, noS8R9_Law2207, noS8R9_Law2212, noS8R9_Law2217⟩
