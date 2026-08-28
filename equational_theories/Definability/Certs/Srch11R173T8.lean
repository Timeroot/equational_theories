import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 9 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `33` equations here, 103 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4600 takes them (3 nodes). -/
def ordS11R173_Law4600 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4600. -/
theorem noS11R173_Law4600 : ∀ v : Magma.tup11R173,
    ¬ @Equation4600 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4600) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4600) (by native_decide) v.1 v.2
    ((@Law4600.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4601 takes them (3 nodes). -/
def ordS11R173_Law4601 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4601. -/
theorem noS11R173_Law4601 : ∀ v : Magma.tup11R173,
    ¬ @Equation4601 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4601) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4601) (by native_decide) v.1 v.2
    ((@Law4601.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4602 takes them (4 nodes). -/
def ordS11R173_Law4602 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4602. -/
theorem noS11R173_Law4602 : ∀ v : Magma.tup11R173,
    ¬ @Equation4602 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4602) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4602) (by native_decide) v.1 v.2
    ((@Law4602.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4603 takes them (3 nodes). -/
def ordS11R173_Law4603 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4603. -/
theorem noS11R173_Law4603 : ∀ v : Magma.tup11R173,
    ¬ @Equation4603 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4603) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4603) (by native_decide) v.1 v.2
    ((@Law4603.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4604 takes them (3 nodes). -/
def ordS11R173_Law4604 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4604. -/
theorem noS11R173_Law4604 : ∀ v : Magma.tup11R173,
    ¬ @Equation4604 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4604) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4604) (by native_decide) v.1 v.2
    ((@Law4604.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4606 takes them (3 nodes). -/
def ordS11R173_Law4606 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4606. -/
theorem noS11R173_Law4606 : ∀ v : Magma.tup11R173,
    ¬ @Equation4606 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4606) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4606) (by native_decide) v.1 v.2
    ((@Law4606.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4611 takes them (3 nodes). -/
def ordS11R173_Law4611 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4611. -/
theorem noS11R173_Law4611 : ∀ v : Magma.tup11R173,
    ¬ @Equation4611 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4611) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4611) (by native_decide) v.1 v.2
    ((@Law4611.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4615 takes them (3 nodes). -/
def ordS11R173_Law4615 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4615. -/
theorem noS11R173_Law4615 : ∀ v : Magma.tup11R173,
    ¬ @Equation4615 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4615) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4615) (by native_decide) v.1 v.2
    ((@Law4615.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4619 takes them (3 nodes). -/
def ordS11R173_Law4619 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4619. -/
theorem noS11R173_Law4619 : ∀ v : Magma.tup11R173,
    ¬ @Equation4619 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4619) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4619) (by native_decide) v.1 v.2
    ((@Law4619.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4622 takes them (3 nodes). -/
def ordS11R173_Law4622 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4622. -/
theorem noS11R173_Law4622 : ∀ v : Magma.tup11R173,
    ¬ @Equation4622 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4622) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4622) (by native_decide) v.1 v.2
    ((@Law4622.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4625 takes them (3 nodes). -/
def ordS11R173_Law4625 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4625. -/
theorem noS11R173_Law4625 : ∀ v : Magma.tup11R173,
    ¬ @Equation4625 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4625) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4625) (by native_decide) v.1 v.2
    ((@Law4625.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (3 nodes). -/
def ordS11R173_Law4629 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4629. -/
theorem noS11R173_Law4629 : ∀ v : Magma.tup11R173,
    ¬ @Equation4629 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4630 takes them (3 nodes). -/
def ordS11R173_Law4630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4630. -/
theorem noS11R173_Law4630 : ∀ v : Magma.tup11R173,
    ¬ @Equation4630 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4630) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4630) (by native_decide) v.1 v.2
    ((@Law4630.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4631 takes them (4 nodes). -/
def ordS11R173_Law4631 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4631. -/
theorem noS11R173_Law4631 : ∀ v : Magma.tup11R173,
    ¬ @Equation4631 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4631) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4631) (by native_decide) v.1 v.2
    ((@Law4631.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4632 takes them (3 nodes). -/
def ordS11R173_Law4632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4632. -/
theorem noS11R173_Law4632 : ∀ v : Magma.tup11R173,
    ¬ @Equation4632 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4632) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4632) (by native_decide) v.1 v.2
    ((@Law4632.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4633 takes them (3 nodes). -/
def ordS11R173_Law4633 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4633. -/
theorem noS11R173_Law4633 : ∀ v : Magma.tup11R173,
    ¬ @Equation4633 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4633) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4633) (by native_decide) v.1 v.2
    ((@Law4633.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4634 takes them (3 nodes). -/
def ordS11R173_Law4634 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4634. -/
theorem noS11R173_Law4634 : ∀ v : Magma.tup11R173,
    ¬ @Equation4634 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4634) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4634) (by native_decide) v.1 v.2
    ((@Law4634.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4638 takes them (3 nodes). -/
def ordS11R173_Law4638 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4638. -/
theorem noS11R173_Law4638 : ∀ v : Magma.tup11R173,
    ¬ @Equation4638 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4638) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4638) (by native_decide) v.1 v.2
    ((@Law4638.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4642 takes them (3 nodes). -/
def ordS11R173_Law4642 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4642. -/
theorem noS11R173_Law4642 : ∀ v : Magma.tup11R173,
    ¬ @Equation4642 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4642) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4642) (by native_decide) v.1 v.2
    ((@Law4642.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4645 takes them (3 nodes). -/
def ordS11R173_Law4645 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4645. -/
theorem noS11R173_Law4645 : ∀ v : Magma.tup11R173,
    ¬ @Equation4645 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4645) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4645) (by native_decide) v.1 v.2
    ((@Law4645.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4649 takes them (3 nodes). -/
def ordS11R173_Law4649 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4649. -/
theorem noS11R173_Law4649 : ∀ v : Magma.tup11R173,
    ¬ @Equation4649 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4649) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4649) (by native_decide) v.1 v.2
    ((@Law4649.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4654 takes them (3 nodes). -/
def ordS11R173_Law4654 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4654. -/
theorem noS11R173_Law4654 : ∀ v : Magma.tup11R173,
    ¬ @Equation4654 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4654) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4654) (by native_decide) v.1 v.2
    ((@Law4654.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4655 takes them (4 nodes). -/
def ordS11R173_Law4655 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4655. -/
theorem noS11R173_Law4655 : ∀ v : Magma.tup11R173,
    ¬ @Equation4655 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4655) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4655) (by native_decide) v.1 v.2
    ((@Law4655.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4657 takes them (3 nodes). -/
def ordS11R173_Law4657 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4657. -/
theorem noS11R173_Law4657 : ∀ v : Magma.tup11R173,
    ¬ @Equation4657 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4657) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4657) (by native_decide) v.1 v.2
    ((@Law4657.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4663 takes them (3 nodes). -/
def ordS11R173_Law4663 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4663. -/
theorem noS11R173_Law4663 : ∀ v : Magma.tup11R173,
    ¬ @Equation4663 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4663) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4663) (by native_decide) v.1 v.2
    ((@Law4663.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4666 takes them (3 nodes). -/
def ordS11R173_Law4666 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4666. -/
theorem noS11R173_Law4666 : ∀ v : Magma.tup11R173,
    ¬ @Equation4666 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4666) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4666) (by native_decide) v.1 v.2
    ((@Law4666.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4669 takes them (3 nodes). -/
def ordS11R173_Law4669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4669. -/
theorem noS11R173_Law4669 : ∀ v : Magma.tup11R173,
    ¬ @Equation4669 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4669) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4669) (by native_decide) v.1 v.2
    ((@Law4669.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4672 takes them (3 nodes). -/
def ordS11R173_Law4672 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4672. -/
theorem noS11R173_Law4672 : ∀ v : Magma.tup11R173,
    ¬ @Equation4672 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4672) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4672) (by native_decide) v.1 v.2
    ((@Law4672.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (3 nodes). -/
def ordS11R173_Law4673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4673. -/
theorem noS11R173_Law4673 : ∀ v : Magma.tup11R173,
    ¬ @Equation4673 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4674 takes them (3 nodes). -/
def ordS11R173_Law4674 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4674. -/
theorem noS11R173_Law4674 : ∀ v : Magma.tup11R173,
    ¬ @Equation4674 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4674) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4674) (by native_decide) v.1 v.2
    ((@Law4674.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4675 takes them (4 nodes). -/
def ordS11R173_Law4675 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4675. -/
theorem noS11R173_Law4675 : ∀ v : Magma.tup11R173,
    ¬ @Equation4675 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4675) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4675) (by native_decide) v.1 v.2
    ((@Law4675.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4682 takes them (3 nodes). -/
def ordS11R173_Law4682 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4682. -/
theorem noS11R173_Law4682 : ∀ v : Magma.tup11R173,
    ¬ @Equation4682 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4682) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4682) (by native_decide) v.1 v.2
    ((@Law4682.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4689 takes them (3 nodes). -/
def ordS11R173_Law4689 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4689. -/
theorem noS11R173_Law4689 : ∀ v : Magma.tup11R173,
    ¬ @Equation4689 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4689) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law4689) (by native_decide) v.1 v.2
    ((@Law4689.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `33` equations. -/
theorem srch11R173_refutes_8 :
    FamilyRefutes Magma.srch11R173 [
      4600, 4601, 4602, 4603, 4604, 4606, 4611, 4615, 4619, 4622, 4625, 4629, 4630, 4631, 4632,
      4633, 4634, 4638, 4642, 4645, 4649, 4654, 4655, 4657, 4663, 4666, 4669, 4672, 4673, 4674,
      4675, 4682, 4689
    ] :=
  ⟨noS11R173_Law4600, noS11R173_Law4601, noS11R173_Law4602, noS11R173_Law4603, noS11R173_Law4604, noS11R173_Law4606, noS11R173_Law4611, noS11R173_Law4615, noS11R173_Law4619, noS11R173_Law4622, noS11R173_Law4625, noS11R173_Law4629, noS11R173_Law4630, noS11R173_Law4631, noS11R173_Law4632, noS11R173_Law4633, noS11R173_Law4634, noS11R173_Law4638, noS11R173_Law4642, noS11R173_Law4645, noS11R173_Law4649, noS11R173_Law4654, noS11R173_Law4655, noS11R173_Law4657, noS11R173_Law4663, noS11R173_Law4666, noS11R173_Law4669, noS11R173_Law4672, noS11R173_Law4673, noS11R173_Law4674, noS11R173_Law4675, noS11R173_Law4682, noS11R173_Law4689⟩
