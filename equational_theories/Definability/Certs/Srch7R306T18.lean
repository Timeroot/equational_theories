import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 19 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 1,073 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1977 takes them (436 nodes). -/
def ordS7R306_Law1977 : List (Fin 7) := [2, 1, 3, 5, 4, 6, 0]

/-- No member of the class satisfies equation 1977. -/
theorem noS7R306_Law1977 : ∀ v : Magma.tup7R306,
    ¬ @Equation1977 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1977) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law1977) (by native_decide) v.1 v.2
    ((@Law1977.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2070 takes them (179 nodes). -/
def ordS7R306_Law2070 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2070. -/
theorem noS7R306_Law2070 : ∀ v : Magma.tup7R306,
    ¬ @Equation2070 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2070) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law2070) (by native_decide) v.1 v.2
    ((@Law2070.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2128 takes them (458 nodes). -/
def ordS7R306_Law2128 : List (Fin 7) := [1, 0, 4, 6, 3, 2, 5]

/-- No member of the class satisfies equation 2128. -/
theorem noS7R306_Law2128 : ∀ v : Magma.tup7R306,
    ¬ @Equation2128 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2128) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law2128) (by native_decide) v.1 v.2
    ((@Law2128.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch7R306_refutes_18 :
    FamilyRefutes Magma.srch7R306 [
      1977, 2070, 2128
    ] :=
  ⟨noS7R306_Law1977, noS7R306_Law2070, noS7R306_Law2128⟩
