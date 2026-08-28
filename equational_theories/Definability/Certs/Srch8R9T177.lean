import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 178 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `8`
equations here, 2,566 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3130 takes them (1165 nodes). -/
def ordS8R9_Law3130 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3130. -/
theorem noS8R9_Law3130 : ∀ v : Magma.tup8R9,
    ¬ @Equation3130 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3130) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3130) (by native_decide) v.1 v.2
    ((@Law3130.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3134 takes them (366 nodes). -/
def ordS8R9_Law3134 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3134. -/
theorem noS8R9_Law3134 : ∀ v : Magma.tup8R9,
    ¬ @Equation3134 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3134) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3134) (by native_decide) v.1 v.2
    ((@Law3134.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3145 takes them (64 nodes). -/
def ordS8R9_Law3145 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3145. -/
theorem noS8R9_Law3145 : ∀ v : Magma.tup8R9,
    ¬ @Equation3145 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3145) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3145) (by native_decide) v.1 v.2
    ((@Law3145.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3163 takes them (73 nodes). -/
def ordS8R9_Law3163 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3163. -/
theorem noS8R9_Law3163 : ∀ v : Magma.tup8R9,
    ¬ @Equation3163 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3163) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3163) (by native_decide) v.1 v.2
    ((@Law3163.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3167 takes them (741 nodes). -/
def ordS8R9_Law3167 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3167. -/
theorem noS8R9_Law3167 : ∀ v : Magma.tup8R9,
    ¬ @Equation3167 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3167) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3167) (by native_decide) v.1 v.2
    ((@Law3167.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3171 takes them (9 nodes). -/
def ordS8R9_Law3171 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3171. -/
theorem noS8R9_Law3171 : ∀ v : Magma.tup8R9,
    ¬ @Equation3171 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3171) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3171) (by native_decide) v.1 v.2
    ((@Law3171.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3184 takes them (84 nodes). -/
def ordS8R9_Law3184 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3184. -/
theorem noS8R9_Law3184 : ∀ v : Magma.tup8R9,
    ¬ @Equation3184 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3184) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3184) (by native_decide) v.1 v.2
    ((@Law3184.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3188 takes them (64 nodes). -/
def ordS8R9_Law3188 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3188. -/
theorem noS8R9_Law3188 : ∀ v : Magma.tup8R9,
    ¬ @Equation3188 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3188) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3188) (by native_decide) v.1 v.2
    ((@Law3188.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch8R9_refutes_177 :
    FamilyRefutes Magma.srch8R9 [
      3130, 3134, 3145, 3163, 3167, 3171, 3184, 3188
    ] :=
  ⟨noS8R9_Law3130, noS8R9_Law3134, noS8R9_Law3145, noS8R9_Law3163, noS8R9_Law3167, noS8R9_Law3171, noS8R9_Law3184, noS8R9_Law3188⟩
