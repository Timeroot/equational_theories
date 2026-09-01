import equational_theories.Definability.Srch_SR14

/-!
# Structural certificate targets: `Magma.srchR14` (part 1 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR14_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,235 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR14_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1285 takes them (1332 nodes). -/
def ordSR14_Law1285 : List (Fin 6) := [4, 3, 1, 2, 5, 0]

/-- No member of the class satisfies equation 1285. -/
theorem noSR14_Law1285 : ∀ v : Magma.tupR14,
    ¬ @Equation1285 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1285) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 2)
    (ord := ordSR14_Law1285) (by native_decide) v.1 v.2
    ((@Law1285.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1374 takes them (189 nodes). -/
def ordSR14_Law1374 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1374. -/
theorem noSR14_Law1374 : ∀ v : Magma.tupR14,
    ¬ @Equation1374 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1374) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1374) (by native_decide) v.1 v.2
    ((@Law1374.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1467 takes them (197 nodes). -/
def ordSR14_Law1467 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1467. -/
theorem noSR14_Law1467 : ∀ v : Magma.tupR14,
    ¬ @Equation1467 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1467) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1467) (by native_decide) v.1 v.2
    ((@Law1467.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1660 takes them (342 nodes). -/
def ordSR14_Law1660 : List (Fin 6) := [5, 3, 1, 4, 2, 0]

/-- No member of the class satisfies equation 1660. -/
theorem noSR14_Law1660 : ∀ v : Magma.tupR14,
    ¬ @Equation1660 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1660) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1660) (by native_decide) v.1 v.2
    ((@Law1660.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1668 takes them (361 nodes). -/
def ordSR14_Law1668 : List (Fin 6) := [4, 5, 2, 3, 1, 0]

/-- No member of the class satisfies equation 1668. -/
theorem noSR14_Law1668 : ∀ v : Magma.tupR14,
    ¬ @Equation1668 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1668) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1668) (by native_decide) v.1 v.2
    ((@Law1668.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1721 takes them (715 nodes). -/
def ordSR14_Law1721 : List (Fin 6) := [4, 3, 0, 1, 2, 5]

/-- No member of the class satisfies equation 1721. -/
theorem noSR14_Law1721 : ∀ v : Magma.tupR14,
    ¬ @Equation1721 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1721) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 2)
    (ord := ordSR14_Law1721) (by native_decide) v.1 v.2
    ((@Law1721.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1793 takes them (99 nodes). -/
def ordSR14_Law1793 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1793. -/
theorem noSR14_Law1793 : ∀ v : Magma.tupR14,
    ¬ @Equation1793 (Fin 6) (Magma.srchR14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1793) (E := SR14.E) (tr := SR14.tr) (z := SR14.z)
    (st := SR14.st) (X := SR14.X) (envs := Magma.envsRed 6 SR14.E 3)
    (ord := ordSR14_Law1793) (by native_decide) v.1 v.2
    ((@Law1793.models_iff (Fin 6) (Magma.srchR14 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srchR14_refutes_0 :
    FamilyRefutes Magma.srchR14 [
      1285, 1374, 1467, 1660, 1668, 1721, 1793
    ] :=
  ⟨noSR14_Law1285, noSR14_Law1374, noSR14_Law1467, noSR14_Law1660, noSR14_Law1668, noSR14_Law1721, noSR14_Law1793⟩
