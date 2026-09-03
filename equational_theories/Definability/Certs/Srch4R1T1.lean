import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 2 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `6`
equations here, 2,773 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 706 takes them (808 nodes). -/
def ordS4R1_Law706 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 706. -/
theorem noS4R1_Law706 : ∀ v : Magma.tup4R1,
    ¬ @Equation706 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law706) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law706) (by native_decide) v.1 v.2
    ((@Law706.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 727 takes them (156 nodes). -/
def ordS4R1_Law727 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 727. -/
theorem noS4R1_Law727 : ∀ v : Magma.tup4R1,
    ¬ @Equation727 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law727) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law727) (by native_decide) v.1 v.2
    ((@Law727.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 960 takes them (261 nodes). -/
def ordS4R1_Law960 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 960. -/
theorem noS4R1_Law960 : ∀ v : Magma.tup4R1,
    ¬ @Equation960 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law960) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law960) (by native_decide) v.1 v.2
    ((@Law960.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 964 takes them (196 nodes). -/
def ordS4R1_Law964 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 964. -/
theorem noS4R1_Law964 : ∀ v : Magma.tup4R1,
    ¬ @Equation964 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law964) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law964) (by native_decide) v.1 v.2
    ((@Law964.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1085 takes them (998 nodes). -/
def ordS4R1_Law1085 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1085. -/
theorem noS4R1_Law1085 : ∀ v : Magma.tup4R1,
    ¬ @Equation1085 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1085) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1085) (by native_decide) v.1 v.2
    ((@Law1085.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1096 takes them (354 nodes). -/
def ordS4R1_Law1096 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1096. -/
theorem noS4R1_Law1096 : ∀ v : Magma.tup4R1,
    ¬ @Equation1096 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1096) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1096) (by native_decide) v.1 v.2
    ((@Law1096.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch4R1_refutes_1 :
    FamilyRefutes Magma.srch4R1 [
      706, 727, 960, 964, 1085, 1096
    ] :=
  ⟨noS4R1_Law706, noS4R1_Law727, noS4R1_Law960, noS4R1_Law964, noS4R1_Law1085, noS4R1_Law1096⟩
