import equational_theories.Definability.Srch_S10R400

/-!
# Structural certificate targets: `Magma.srch10R400` (part 3 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 2,494 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3573 takes them (845 nodes). -/
def ordS10R400_Law3573 : List (Fin 11) := [10, 0, 3, 2, 5, 4, 6, 9, 1, 7, 8]

/-- No member of the class satisfies equation 3573. -/
theorem noS10R400_Law3573 : ∀ v : Magma.tup10R400,
    ¬ @Equation3573 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3573) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 3)
    (ord := ordS10R400_Law3573) (by native_decide) v.1 v.2
    ((@Law3573.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3751 takes them (446 nodes). -/
def ordS10R400_Law3751 : List (Fin 11) := [10, 0, 5, 7, 9, 4, 1, 3, 6, 8, 2]

/-- No member of the class satisfies equation 3751. -/
theorem noS10R400_Law3751 : ∀ v : Magma.tup10R400,
    ¬ @Equation3751 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3751) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3751) (by native_decide) v.1 v.2
    ((@Law3751.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3758 takes them (326 nodes). -/
def ordS10R400_Law3758 : List (Fin 11) := [6, 10, 7, 0, 8, 1, 5, 9, 2, 4, 3]

/-- No member of the class satisfies equation 3758. -/
theorem noS10R400_Law3758 : ∀ v : Magma.tup10R400,
    ¬ @Equation3758 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3758) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3758) (by native_decide) v.1 v.2
    ((@Law3758.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3951 takes them (877 nodes). -/
def ordS10R400_Law3951 : List (Fin 11) := [0, 8, 6, 4, 3, 1, 5, 9, 2, 7, 10]

/-- No member of the class satisfies equation 3951. -/
theorem noS10R400_Law3951 : ∀ v : Magma.tup10R400,
    ¬ @Equation3951 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3951) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3951) (by native_decide) v.1 v.2
    ((@Law3951.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch10R400_refutes_2 :
    FamilyRefutes Magma.srch10R400 [
      3573, 3751, 3758, 3951
    ] :=
  ⟨noS10R400_Law3573, noS10R400_Law3751, noS10R400_Law3758, noS10R400_Law3951⟩
