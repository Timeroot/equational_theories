import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 57 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 2,871 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4620 takes them (638 nodes). -/
def ordS7R12_Law4620 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4620. -/
theorem noS7R12_Law4620 : ∀ v : Magma.tup7R12,
    ¬ @Equation4620 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4620) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4620) (by native_decide) v.1 v.2
    ((@Law4620.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4625 takes them (536 nodes). -/
def ordS7R12_Law4625 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4625. -/
theorem noS7R12_Law4625 : ∀ v : Magma.tup7R12,
    ¬ @Equation4625 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4625) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4625) (by native_decide) v.1 v.2
    ((@Law4625.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4626 takes them (629 nodes). -/
def ordS7R12_Law4626 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4626. -/
theorem noS7R12_Law4626 : ∀ v : Magma.tup7R12,
    ¬ @Equation4626 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4626) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4626) (by native_decide) v.1 v.2
    ((@Law4626.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (271 nodes). -/
def ordS7R12_Law4629 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4629. -/
theorem noS7R12_Law4629 : ∀ v : Magma.tup7R12,
    ¬ @Equation4629 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4630 takes them (28 nodes). -/
def ordS7R12_Law4630 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4630. -/
theorem noS7R12_Law4630 : ∀ v : Magma.tup7R12,
    ¬ @Equation4630 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4630) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4630) (by native_decide) v.1 v.2
    ((@Law4630.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4631 takes them (578 nodes). -/
def ordS7R12_Law4631 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4631. -/
theorem noS7R12_Law4631 : ∀ v : Magma.tup7R12,
    ¬ @Equation4631 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4631) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4631) (by native_decide) v.1 v.2
    ((@Law4631.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4632 takes them (79 nodes). -/
def ordS7R12_Law4632 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4632. -/
theorem noS7R12_Law4632 : ∀ v : Magma.tup7R12,
    ¬ @Equation4632 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4632) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4632) (by native_decide) v.1 v.2
    ((@Law4632.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4633 takes them (88 nodes). -/
def ordS7R12_Law4633 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4633. -/
theorem noS7R12_Law4633 : ∀ v : Magma.tup7R12,
    ¬ @Equation4633 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4633) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4633) (by native_decide) v.1 v.2
    ((@Law4633.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4634 takes them (24 nodes). -/
def ordS7R12_Law4634 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4634. -/
theorem noS7R12_Law4634 : ∀ v : Magma.tup7R12,
    ¬ @Equation4634 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4634) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4634) (by native_decide) v.1 v.2
    ((@Law4634.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch7R12_refutes_56 :
    FamilyRefutes Magma.srch7R12 [
      4620, 4625, 4626, 4629, 4630, 4631, 4632, 4633, 4634
    ] :=
  ⟨noS7R12_Law4620, noS7R12_Law4625, noS7R12_Law4626, noS7R12_Law4629, noS7R12_Law4630, noS7R12_Law4631, noS7R12_Law4632, noS7R12_Law4633, noS7R12_Law4634⟩
