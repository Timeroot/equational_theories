import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 10 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `6`
equations here, 3,735 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2866 takes them (1144 nodes). -/
def ordS4R1_Law2866 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2866. -/
theorem noS4R1_Law2866 : ∀ v : Magma.tup4R1,
    ¬ @Equation2866 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2866) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law2866) (by native_decide) v.1 v.2
    ((@Law2866.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2883 takes them (345 nodes). -/
def ordS4R1_Law2883 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2883. -/
theorem noS4R1_Law2883 : ∀ v : Magma.tup4R1,
    ¬ @Equation2883 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2883) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2883) (by native_decide) v.1 v.2
    ((@Law2883.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2887 takes them (345 nodes). -/
def ordS4R1_Law2887 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2887. -/
theorem noS4R1_Law2887 : ∀ v : Magma.tup4R1,
    ¬ @Equation2887 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2887) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2887) (by native_decide) v.1 v.2
    ((@Law2887.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2994 takes them (384 nodes). -/
def ordS4R1_Law2994 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2994. -/
theorem noS4R1_Law2994 : ∀ v : Magma.tup4R1,
    ¬ @Equation2994 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2994) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2994) (by native_decide) v.1 v.2
    ((@Law2994.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3069 takes them (684 nodes). -/
def ordS4R1_Law3069 : List (Fin 8) := [0, 4, 1, 3, 7, 6, 5, 2]

/-- No member of the class satisfies equation 3069. -/
theorem noS4R1_Law3069 : ∀ v : Magma.tup4R1,
    ¬ @Equation3069 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3069) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law3069) (by native_decide) v.1 v.2
    ((@Law3069.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3076 takes them (833 nodes). -/
def ordS4R1_Law3076 : List (Fin 8) := [2, 6, 5, 3, 4, 1, 7, 0]

/-- No member of the class satisfies equation 3076. -/
theorem noS4R1_Law3076 : ∀ v : Magma.tup4R1,
    ¬ @Equation3076 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3076) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law3076) (by native_decide) v.1 v.2
    ((@Law3076.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch4R1_refutes_9 :
    FamilyRefutes Magma.srch4R1 [
      2866, 2883, 2887, 2994, 3069, 3076
    ] :=
  ⟨noS4R1_Law2866, noS4R1_Law2883, noS4R1_Law2887, noS4R1_Law2994, noS4R1_Law3069, noS4R1_Law3076⟩
