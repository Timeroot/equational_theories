import equational_theories.Definability.Srch_S10R401

/-!
# Structural certificate targets: `Magma.srch10R401`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R401_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `17` equations here, 2,475 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R401_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 716 takes them (144 nodes). -/
def ordS10R401_Law716 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 716. -/
theorem noS10R401_Law716 : ∀ v : Magma.tup10R401,
    ¬ @Equation716 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (159 nodes). -/
def ordS10R401_Law919 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 919. -/
theorem noS10R401_Law919 : ∀ v : Magma.tup10R401,
    ¬ @Equation919 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (120 nodes). -/
def ordS10R401_Law1109 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1109. -/
theorem noS10R401_Law1109 : ∀ v : Magma.tup10R401,
    ¬ @Equation1109 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1451 takes them (116 nodes). -/
def ordS10R401_Law1451 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1451. -/
theorem noS10R401_Law1451 : ∀ v : Magma.tup10R401,
    ¬ @Equation1451 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1451) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law1451) (by native_decide) v.1 v.2
    ((@Law1451.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (173 nodes). -/
def ordS10R401_Law1528 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1528. -/
theorem noS10R401_Law1528 : ∀ v : Magma.tup10R401,
    ¬ @Equation1528 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (233 nodes). -/
def ordS10R401_Law1654 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1654. -/
theorem noS10R401_Law1654 : ∀ v : Magma.tup10R401,
    ¬ @Equation1654 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (257 nodes). -/
def ordS10R401_Law1840 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1840. -/
theorem noS10R401_Law1840 : ∀ v : Magma.tup10R401,
    ¬ @Equation1840 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2043 takes them (200 nodes). -/
def ordS10R401_Law2043 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2043. -/
theorem noS10R401_Law2043 : ∀ v : Magma.tup10R401,
    ¬ @Equation2043 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2043) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law2043) (by native_decide) v.1 v.2
    ((@Law2043.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (131 nodes). -/
def ordS10R401_Law2064 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2064. -/
theorem noS10R401_Law2064 : ∀ v : Magma.tup10R401,
    ¬ @Equation2064 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2444 takes them (160 nodes). -/
def ordS10R401_Law2444 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2444. -/
theorem noS10R401_Law2444 : ∀ v : Magma.tup10R401,
    ¬ @Equation2444 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (147 nodes). -/
def ordS10R401_Law2673 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2673. -/
theorem noS10R401_Law2673 : ∀ v : Magma.tup10R401,
    ¬ @Equation2673 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (132 nodes). -/
def ordS10R401_Law2876 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2876. -/
theorem noS10R401_Law2876 : ∀ v : Magma.tup10R401,
    ¬ @Equation2876 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3748 takes them (49 nodes). -/
def ordS10R401_Law3748 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3748. -/
theorem noS10R401_Law3748 : ∀ v : Magma.tup10R401,
    ¬ @Equation3748 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3748) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law3748) (by native_decide) v.1 v.2
    ((@Law3748.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3761 takes them (139 nodes). -/
def ordS10R401_Law3761 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3761. -/
theorem noS10R401_Law3761 : ∀ v : Magma.tup10R401,
    ¬ @Equation3761 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3761) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law3761) (by native_decide) v.1 v.2
    ((@Law3761.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4290 takes them (72 nodes). -/
def ordS10R401_Law4290 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4290. -/
theorem noS10R401_Law4290 : ∀ v : Magma.tup10R401,
    ¬ @Equation4290 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4290) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law4290) (by native_decide) v.1 v.2
    ((@Law4290.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4405 takes them (87 nodes). -/
def ordS10R401_Law4405 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4405. -/
theorem noS10R401_Law4405 : ∀ v : Magma.tup10R401,
    ¬ @Equation4405 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4405) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law4405) (by native_decide) v.1 v.2
    ((@Law4405.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4605 takes them (156 nodes). -/
def ordS10R401_Law4605 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4605. -/
theorem noS10R401_Law4605 : ∀ v : Magma.tup10R401,
    ¬ @Equation4605 (Fin 10) (Magma.srch10R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4605) (E := S10R401.E) (tr := S10R401.tr) (z := S10R401.z)
    (st := S10R401.st) (X := S10R401.X) (envs := Magma.envsRed 10 S10R401.E 2)
    (ord := ordS10R401_Law4605) (by native_decide) v.1 v.2
    ((@Law4605.models_iff (Fin 10) (Magma.srch10R401 v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch10R401_refutes_0 :
    FamilyRefutes Magma.srch10R401 [
      716, 919, 1109, 1451, 1528, 1654, 1840, 2043, 2064, 2444, 2673, 2876, 3748, 3761, 4290,
      4405, 4605
    ] :=
  ⟨noS10R401_Law716, noS10R401_Law919, noS10R401_Law1109, noS10R401_Law1451, noS10R401_Law1528, noS10R401_Law1654, noS10R401_Law1840, noS10R401_Law2043, noS10R401_Law2064, noS10R401_Law2444, noS10R401_Law2673, noS10R401_Law2876, noS10R401_Law3748, noS10R401_Law3761, noS10R401_Law4290, noS10R401_Law4405, noS10R401_Law4605⟩
