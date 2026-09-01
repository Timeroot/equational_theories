import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 23 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `25` equations here, 2,769 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4596 takes them (10 nodes). -/
def ordS7R325_Law4596 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4596. -/
theorem noS7R325_Law4596 : ∀ v : Magma.tup7R325,
    ¬ @Equation4596 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4596) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4596) (by native_decide) v.1 v.2
    ((@Law4596.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4600 takes them (240 nodes). -/
def ordS7R325_Law4600 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4600. -/
theorem noS7R325_Law4600 : ∀ v : Magma.tup7R325,
    ¬ @Equation4600 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4600) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4600) (by native_decide) v.1 v.2
    ((@Law4600.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4602 takes them (100 nodes). -/
def ordS7R325_Law4602 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4602. -/
theorem noS7R325_Law4602 : ∀ v : Magma.tup7R325,
    ¬ @Equation4602 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4602) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4602) (by native_decide) v.1 v.2
    ((@Law4602.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4604 takes them (52 nodes). -/
def ordS7R325_Law4604 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4604. -/
theorem noS7R325_Law4604 : ∀ v : Magma.tup7R325,
    ¬ @Equation4604 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4604) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4604) (by native_decide) v.1 v.2
    ((@Law4604.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4607 takes them (187 nodes). -/
def ordS7R325_Law4607 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4607. -/
theorem noS7R325_Law4607 : ∀ v : Magma.tup7R325,
    ¬ @Equation4607 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4607) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4607) (by native_decide) v.1 v.2
    ((@Law4607.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4610 takes them (16 nodes). -/
def ordS7R325_Law4610 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4610. -/
theorem noS7R325_Law4610 : ∀ v : Magma.tup7R325,
    ¬ @Equation4610 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4610) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4610) (by native_decide) v.1 v.2
    ((@Law4610.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4613 takes them (10 nodes). -/
def ordS7R325_Law4613 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4613. -/
theorem noS7R325_Law4613 : ∀ v : Magma.tup7R325,
    ¬ @Equation4613 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4613) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4613) (by native_decide) v.1 v.2
    ((@Law4613.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4617 takes them (10 nodes). -/
def ordS7R325_Law4617 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4617. -/
theorem noS7R325_Law4617 : ∀ v : Magma.tup7R325,
    ¬ @Equation4617 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4617) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4617) (by native_decide) v.1 v.2
    ((@Law4617.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4618 takes them (16 nodes). -/
def ordS7R325_Law4618 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4618. -/
theorem noS7R325_Law4618 : ∀ v : Magma.tup7R325,
    ¬ @Equation4618 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4618) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4618) (by native_decide) v.1 v.2
    ((@Law4618.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4621 takes them (10 nodes). -/
def ordS7R325_Law4621 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4621. -/
theorem noS7R325_Law4621 : ∀ v : Magma.tup7R325,
    ¬ @Equation4621 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4621) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4621) (by native_decide) v.1 v.2
    ((@Law4621.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4624 takes them (10 nodes). -/
def ordS7R325_Law4624 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4624. -/
theorem noS7R325_Law4624 : ∀ v : Magma.tup7R325,
    ¬ @Equation4624 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4624) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4624) (by native_decide) v.1 v.2
    ((@Law4624.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4625 takes them (58 nodes). -/
def ordS7R325_Law4625 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4625. -/
theorem noS7R325_Law4625 : ∀ v : Magma.tup7R325,
    ¬ @Equation4625 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4625) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4625) (by native_decide) v.1 v.2
    ((@Law4625.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4628 takes them (10 nodes). -/
def ordS7R325_Law4628 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4628. -/
theorem noS7R325_Law4628 : ∀ v : Magma.tup7R325,
    ¬ @Equation4628 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4628) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4628) (by native_decide) v.1 v.2
    ((@Law4628.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4630 takes them (334 nodes). -/
def ordS7R325_Law4630 : List (Fin 9) := [4, 8, 0, 5, 6, 7, 2, 3, 1]

/-- No member of the class satisfies equation 4630. -/
theorem noS7R325_Law4630 : ∀ v : Magma.tup7R325,
    ¬ @Equation4630 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4630) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4630) (by native_decide) v.1 v.2
    ((@Law4630.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4632 takes them (864 nodes). -/
def ordS7R325_Law4632 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4632. -/
theorem noS7R325_Law4632 : ∀ v : Magma.tup7R325,
    ¬ @Equation4632 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4632) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4632) (by native_decide) v.1 v.2
    ((@Law4632.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4634 takes them (240 nodes). -/
def ordS7R325_Law4634 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4634. -/
theorem noS7R325_Law4634 : ∀ v : Magma.tup7R325,
    ¬ @Equation4634 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4634) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4634) (by native_decide) v.1 v.2
    ((@Law4634.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4637 takes them (147 nodes). -/
def ordS7R325_Law4637 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4637. -/
theorem noS7R325_Law4637 : ∀ v : Magma.tup7R325,
    ¬ @Equation4637 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4637) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4637) (by native_decide) v.1 v.2
    ((@Law4637.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4638 takes them (199 nodes). -/
def ordS7R325_Law4638 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4638. -/
theorem noS7R325_Law4638 : ∀ v : Magma.tup7R325,
    ¬ @Equation4638 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4638) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4638) (by native_decide) v.1 v.2
    ((@Law4638.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4641 takes them (10 nodes). -/
def ordS7R325_Law4641 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4641. -/
theorem noS7R325_Law4641 : ∀ v : Magma.tup7R325,
    ¬ @Equation4641 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4641) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4641) (by native_decide) v.1 v.2
    ((@Law4641.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4643 takes them (142 nodes). -/
def ordS7R325_Law4643 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4643. -/
theorem noS7R325_Law4643 : ∀ v : Magma.tup7R325,
    ¬ @Equation4643 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4643) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4643) (by native_decide) v.1 v.2
    ((@Law4643.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4644 takes them (10 nodes). -/
def ordS7R325_Law4644 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4644. -/
theorem noS7R325_Law4644 : ∀ v : Magma.tup7R325,
    ¬ @Equation4644 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4644) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4644) (by native_decide) v.1 v.2
    ((@Law4644.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4648 takes them (10 nodes). -/
def ordS7R325_Law4648 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4648. -/
theorem noS7R325_Law4648 : ∀ v : Magma.tup7R325,
    ¬ @Equation4648 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4648) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4648) (by native_decide) v.1 v.2
    ((@Law4648.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4649 takes them (58 nodes). -/
def ordS7R325_Law4649 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4649. -/
theorem noS7R325_Law4649 : ∀ v : Magma.tup7R325,
    ¬ @Equation4649 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4649) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4649) (by native_decide) v.1 v.2
    ((@Law4649.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4650 takes them (16 nodes). -/
def ordS7R325_Law4650 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4650. -/
theorem noS7R325_Law4650 : ∀ v : Magma.tup7R325,
    ¬ @Equation4650 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4650) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4650) (by native_decide) v.1 v.2
    ((@Law4650.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4653 takes them (10 nodes). -/
def ordS7R325_Law4653 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4653. -/
theorem noS7R325_Law4653 : ∀ v : Magma.tup7R325,
    ¬ @Equation4653 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4653) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4653) (by native_decide) v.1 v.2
    ((@Law4653.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `25` equations. -/
theorem srch7R325_refutes_22 :
    FamilyRefutes Magma.srch7R325 [
      4596, 4600, 4602, 4604, 4607, 4610, 4613, 4617, 4618, 4621, 4624, 4625, 4628, 4630, 4632,
      4634, 4637, 4638, 4641, 4643, 4644, 4648, 4649, 4650, 4653
    ] :=
  ⟨noS7R325_Law4596, noS7R325_Law4600, noS7R325_Law4602, noS7R325_Law4604, noS7R325_Law4607, noS7R325_Law4610, noS7R325_Law4613, noS7R325_Law4617, noS7R325_Law4618, noS7R325_Law4621, noS7R325_Law4624, noS7R325_Law4625, noS7R325_Law4628, noS7R325_Law4630, noS7R325_Law4632, noS7R325_Law4634, noS7R325_Law4637, noS7R325_Law4638, noS7R325_Law4641, noS7R325_Law4643, noS7R325_Law4644, noS7R325_Law4648, noS7R325_Law4649, noS7R325_Law4650, noS7R325_Law4653⟩
