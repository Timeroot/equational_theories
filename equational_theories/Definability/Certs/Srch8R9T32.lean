import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 33 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `4`
equations here, 3,833 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 682 takes them (1016 nodes). -/
def ordS8R9_Law682 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 682. -/
theorem noS8R9_Law682 : ∀ v : Magma.tup8R9,
    ¬ @Equation682 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law682) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law682) (by native_decide) v.1 v.2
    ((@Law682.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 690 takes them (1335 nodes). -/
def ordS8R9_Law690 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 690. -/
theorem noS8R9_Law690 : ∀ v : Magma.tup8R9,
    ¬ @Equation690 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law690) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law690) (by native_decide) v.1 v.2
    ((@Law690.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 694 takes them (741 nodes). -/
def ordS8R9_Law694 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 694. -/
theorem noS8R9_Law694 : ∀ v : Magma.tup8R9,
    ¬ @Equation694 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law694) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law694) (by native_decide) v.1 v.2
    ((@Law694.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 698 takes them (741 nodes). -/
def ordS8R9_Law698 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 698. -/
theorem noS8R9_Law698 : ∀ v : Magma.tup8R9,
    ¬ @Equation698 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law698) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law698) (by native_decide) v.1 v.2
    ((@Law698.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R9_refutes_32 :
    FamilyRefutes Magma.srch8R9 [
      682, 690, 694, 698
    ] :=
  ⟨noS8R9_Law682, noS8R9_Law690, noS8R9_Law694, noS8R9_Law698⟩
