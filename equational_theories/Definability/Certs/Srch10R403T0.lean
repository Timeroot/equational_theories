import equational_theories.Definability.Srch_S10R403

/-!
# Structural certificate targets: `Magma.srch10R403`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R403_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 1,603 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R403_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1075 takes them (833 nodes). -/
def ordS10R403_Law1075 : List (Fin 8) := [1, 0, 4, 7, 6, 3, 2, 5]

/-- No member of the class satisfies equation 1075. -/
theorem noS10R403_Law1075 : ∀ v : Magma.tup10R403,
    ¬ @Equation1075 (Fin 10) (Magma.srch10R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S10R403.E) (tr := S10R403.tr) (z := S10R403.z)
    (st := S10R403.st) (X := S10R403.X) (envs := Magma.envsRed 10 S10R403.E 2)
    (ord := ordS10R403_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 10) (Magma.srch10R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (770 nodes). -/
def ordS10R403_Law2457 : List (Fin 8) := [1, 6, 0, 7, 2, 5, 3, 4]

/-- No member of the class satisfies equation 2457. -/
theorem noS10R403_Law2457 : ∀ v : Magma.tup10R403,
    ¬ @Equation2457 (Fin 10) (Magma.srch10R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S10R403.E) (tr := S10R403.tr) (z := S10R403.z)
    (st := S10R403.st) (X := S10R403.X) (envs := Magma.envsRed 10 S10R403.E 2)
    (ord := ordS10R403_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 10) (Magma.srch10R403 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R403_refutes_0 :
    FamilyRefutes Magma.srch10R403 [
      1075, 2457
    ] :=
  ⟨noS10R403_Law1075, noS10R403_Law2457⟩
