import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 15 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 1,074 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1504 takes them (255 nodes). -/
def ordS7R306_Law1504 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1504. -/
theorem noS7R306_Law1504 : ∀ v : Magma.tup7R306,
    ¬ @Equation1504 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1504) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law1504) (by native_decide) v.1 v.2
    ((@Law1504.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1519 takes them (468 nodes). -/
def ordS7R306_Law1519 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1519. -/
theorem noS7R306_Law1519 : ∀ v : Magma.tup7R306,
    ¬ @Equation1519 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1519) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law1519) (by native_decide) v.1 v.2
    ((@Law1519.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1558 takes them (351 nodes). -/
def ordS7R306_Law1558 : List (Fin 7) := [3, 4, 2, 1, 5, 0, 6]

/-- No member of the class satisfies equation 1558. -/
theorem noS7R306_Law1558 : ∀ v : Magma.tup7R306,
    ¬ @Equation1558 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1558) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law1558) (by native_decide) v.1 v.2
    ((@Law1558.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch7R306_refutes_14 :
    FamilyRefutes Magma.srch7R306 [
      1504, 1519, 1558
    ] :=
  ⟨noS7R306_Law1504, noS7R306_Law1519, noS7R306_Law1558⟩
