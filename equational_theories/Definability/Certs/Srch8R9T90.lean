import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 91 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 2,693 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1763 takes them (1925 nodes). -/
def ordS8R9_Law1763 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1763. -/
theorem noS8R9_Law1763 : ∀ v : Magma.tup8R9,
    ¬ @Equation1763 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1763) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law1763) (by native_decide) v.1 v.2
    ((@Law1763.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1767 takes them (768 nodes). -/
def ordS8R9_Law1767 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1767. -/
theorem noS8R9_Law1767 : ∀ v : Magma.tup8R9,
    ¬ @Equation1767 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1767) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law1767) (by native_decide) v.1 v.2
    ((@Law1767.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R9_refutes_90 :
    FamilyRefutes Magma.srch8R9 [
      1763, 1767
    ] :=
  ⟨noS8R9_Law1763, noS8R9_Law1767⟩
