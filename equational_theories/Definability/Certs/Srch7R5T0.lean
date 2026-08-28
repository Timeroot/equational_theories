import equational_theories.Definability.Srch_S7R5

/-!
# Structural certificate targets: `Magma.srch7R5` (part 1 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R5_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `4`
equations here, 3,736 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R5_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 127 takes them (905 nodes). -/
def ordS7R5_Law127 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 127. -/
theorem noS7R5_Law127 : ∀ v : Magma.tup7R5,
    ¬ @Equation127 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 2)
    (ord := ordS7R5_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (974 nodes). -/
def ordS7R5_Law160 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 160. -/
theorem noS7R5_Law160 : ∀ v : Magma.tup7R5,
    ¬ @Equation160 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 2)
    (ord := ordS7R5_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (871 nodes). -/
def ordS7R5_Law179 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 179. -/
theorem noS7R5_Law179 : ∀ v : Magma.tup7R5,
    ¬ @Equation179 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 2)
    (ord := ordS7R5_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (986 nodes). -/
def ordS7R5_Law212 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 212. -/
theorem noS7R5_Law212 : ∀ v : Magma.tup7R5,
    ¬ @Equation212 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 2)
    (ord := ordS7R5_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch7R5_refutes_0 :
    FamilyRefutes Magma.srch7R5 [
      127, 160, 179, 212
    ] :=
  ⟨noS7R5_Law127, noS7R5_Law160, noS7R5_Law179, noS7R5_Law212⟩
