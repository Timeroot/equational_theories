import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 7 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `5`
equations here, 3,475 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1428 takes them (953 nodes). -/
def ordSR30_Law1428 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1428. -/
theorem noSR30_Law1428 : ∀ v : Magma.tupR30,
    ¬ @Equation1428 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1428) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1428) (by native_decide) v.1 v.2
    ((@Law1428.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (465 nodes). -/
def ordSR30_Law1632 : List (Fin 10) := [4, 0, 3, 8, 6, 2, 1, 9, 7, 5]

/-- No member of the class satisfies equation 1632. -/
theorem noSR30_Law1632 : ∀ v : Magma.tupR30,
    ¬ @Equation1632 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1634 takes them (893 nodes). -/
def ordSR30_Law1634 : List (Fin 10) := [7, 4, 1, 3, 0, 2, 5, 8, 6, 9]

/-- No member of the class satisfies equation 1634. -/
theorem noSR30_Law1634 : ∀ v : Magma.tupR30,
    ¬ @Equation1634 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1634) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1634) (by native_decide) v.1 v.2
    ((@Law1634.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (563 nodes). -/
def ordSR30_Law1654 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1654. -/
theorem noSR30_Law1654 : ∀ v : Magma.tupR30,
    ¬ @Equation1654 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (601 nodes). -/
def ordSR30_Law1691 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1691. -/
theorem noSR30_Law1691 : ∀ v : Magma.tupR30,
    ¬ @Equation1691 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srchR30_refutes_6 :
    FamilyRefutes Magma.srchR30 [
      1428, 1632, 1634, 1654, 1691
    ] :=
  ⟨noSR30_Law1428, noSR30_Law1632, noSR30_Law1634, noSR30_Law1654, noSR30_Law1691⟩
