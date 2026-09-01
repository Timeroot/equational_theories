import equational_theories.Definability.Srch_SR14

/-!
# Structural certificate targets: `Magma.srchR14` (part 2 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR14_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `8`
equations here, 3,666 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR14_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1851 takes them (787 nodes). -/
def ordSR14_Law1851 : List (Fin 6) := [0, 2, 1, 5, 3, 4]

/-- No member of the class satisfies equation 1851. -/
theorem noSR14_Law1851 : ∀ v : Magma.tupR14,
    ¬ @Equation1851 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1851) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 2)
    (ord := ordSR14_Law1851) (by native_decide) v.1 v.2
    ((@Law1851.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1871 takes them (359 nodes). -/
def ordSR14_Law1871 : List (Fin 6) := [1, 4, 5, 2, 3, 0]

/-- No member of the class satisfies equation 1871. -/
theorem noSR14_Law1871 : ∀ v : Magma.tupR14,
    ¬ @Equation1871 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1871) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1871) (by native_decide) v.1 v.2
    ((@Law1871.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1875 takes them (338 nodes). -/
def ordSR14_Law1875 : List (Fin 6) := [5, 1, 4, 3, 2, 0]

/-- No member of the class satisfies equation 1875. -/
theorem noSR14_Law1875 : ∀ v : Magma.tupR14,
    ¬ @Equation1875 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1875) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1875) (by native_decide) v.1 v.2
    ((@Law1875.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1876 takes them (99 nodes). -/
def ordSR14_Law1876 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1876. -/
theorem noSR14_Law1876 : ∀ v : Magma.tupR14,
    ¬ @Equation1876 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1876) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1876) (by native_decide) v.1 v.2
    ((@Law1876.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2186 takes them (197 nodes). -/
def ordSR14_Law2186 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2186. -/
theorem noSR14_Law2186 : ∀ v : Magma.tupR14,
    ¬ @Equation2186 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2186) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law2186) (by native_decide) v.1 v.2
    ((@Law2186.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2244 takes them (1333 nodes). -/
def ordSR14_Law2244 : List (Fin 6) := [5, 3, 2, 4, 1, 0]

/-- No member of the class satisfies equation 2244. -/
theorem noSR14_Law2244 : ∀ v : Magma.tupR14,
    ¬ @Equation2244 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2244) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 2)
    (ord := ordSR14_Law2244) (by native_decide) v.1 v.2
    ((@Law2244.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2279 takes them (189 nodes). -/
def ordSR14_Law2279 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2279. -/
theorem noSR14_Law2279 : ∀ v : Magma.tupR14,
    ¬ @Equation2279 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2279) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law2279) (by native_decide) v.1 v.2
    ((@Law2279.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3474 takes them (364 nodes). -/
def ordSR14_Law3474 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3474. -/
theorem noSR14_Law3474 : ∀ v : Magma.tupR14,
    ¬ @Equation3474 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3474) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 2)
    (ord := ordSR14_Law3474) (by native_decide) v.1 v.2
    ((@Law3474.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srchR14_refutes_1 :
    FamilyRefutes Magma.srchR14 [
      1851, 1871, 1875, 1876, 2186, 2244, 2279, 3474
    ] :=
  ⟨noSR14_Law1851, noSR14_Law1871, noSR14_Law1875, noSR14_Law1876, noSR14_Law2186, noSR14_Law2244, noSR14_Law2279, noSR14_Law3474⟩
