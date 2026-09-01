import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 10 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 715 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1152 takes them (310 nodes). -/
def ordS7R306_Law1152 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1152. -/
theorem noS7R306_Law1152 : ∀ v : Magma.tup7R306,
    ¬ @Equation1152 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1152) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law1152) (by native_decide) v.1 v.2
    ((@Law1152.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1155 takes them (405 nodes). -/
def ordS7R306_Law1155 : List (Fin 7) := [6, 2, 1, 5, 4, 0, 3]

/-- No member of the class satisfies equation 1155. -/
theorem noS7R306_Law1155 : ∀ v : Magma.tup7R306,
    ¬ @Equation1155 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1155) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law1155) (by native_decide) v.1 v.2
    ((@Law1155.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch7R306_refutes_9 :
    FamilyRefutes Magma.srch7R306 [
      1152, 1155
    ] :=
  ⟨noS7R306_Law1152, noS7R306_Law1155⟩
