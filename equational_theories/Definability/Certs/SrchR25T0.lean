import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 1 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `16`
equations here, 3,130 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 16 takes them (125 nodes). -/
def ordSR25_Law16 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 16. -/
theorem noSR25_Law16 : ∀ v : Magma.tupR25,
    ¬ @Equation16 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (137 nodes). -/
def ordSR25_Law26 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 26. -/
theorem noSR25_Law26 : ∀ v : Magma.tupR25,
    ¬ @Equation26 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 72 takes them (225 nodes). -/
def ordSR25_Law72 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 72. -/
theorem noSR25_Law72 : ∀ v : Magma.tupR25,
    ¬ @Equation72 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law72) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law72) (by native_decide) v.1 v.2
    ((@Law72.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 258 takes them (217 nodes). -/
def ordSR25_Law258 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 258. -/
theorem noSR25_Law258 : ∀ v : Magma.tupR25,
    ¬ @Equation258 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law258) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law258) (by native_decide) v.1 v.2
    ((@Law258.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 310 takes them (163 nodes). -/
def ordSR25_Law310 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 310. -/
theorem noSR25_Law310 : ∀ v : Magma.tupR25,
    ¬ @Equation310 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law310) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law310) (by native_decide) v.1 v.2
    ((@Law310.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 367 takes them (163 nodes). -/
def ordSR25_Law367 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 367. -/
theorem noSR25_Law367 : ∀ v : Magma.tupR25,
    ¬ @Equation367 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law367) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law367) (by native_decide) v.1 v.2
    ((@Law367.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 427 takes them (226 nodes). -/
def ordSR25_Law427 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 427. -/
theorem noSR25_Law427 : ∀ v : Magma.tupR25,
    ¬ @Equation427 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (364 nodes). -/
def ordSR25_Law466 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 466. -/
theorem noSR25_Law466 : ∀ v : Magma.tupR25,
    ¬ @Equation466 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (223 nodes). -/
def ordSR25_Law500 : List (Fin 8) := [1, 2, 4, 0, 7, 6, 5, 3]

/-- No member of the class satisfies equation 500. -/
theorem noSR25_Law500 : ∀ v : Magma.tupR25,
    ¬ @Equation500 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 513 takes them (183 nodes). -/
def ordSR25_Law513 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 513. -/
theorem noSR25_Law513 : ∀ v : Magma.tupR25,
    ¬ @Equation513 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law513) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law513) (by native_decide) v.1 v.2
    ((@Law513.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (125 nodes). -/
def ordSR25_Law528 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 528. -/
theorem noSR25_Law528 : ∀ v : Magma.tupR25,
    ¬ @Equation528 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (125 nodes). -/
def ordSR25_Law575 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 575. -/
theorem noSR25_Law575 : ∀ v : Magma.tupR25,
    ¬ @Equation575 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 833 takes them (194 nodes). -/
def ordSR25_Law833 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 833. -/
theorem noSR25_Law833 : ∀ v : Magma.tupR25,
    ¬ @Equation833 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law833) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law833) (by native_decide) v.1 v.2
    ((@Law833.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 836 takes them (266 nodes). -/
def ordSR25_Law836 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 836. -/
theorem noSR25_Law836 : ∀ v : Magma.tupR25,
    ¬ @Equation836 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (229 nodes). -/
def ordSR25_Law843 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 843. -/
theorem noSR25_Law843 : ∀ v : Magma.tupR25,
    ¬ @Equation843 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 909 takes them (165 nodes). -/
def ordSR25_Law909 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 909. -/
theorem noSR25_Law909 : ∀ v : Magma.tupR25,
    ¬ @Equation909 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law909) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law909) (by native_decide) v.1 v.2
    ((@Law909.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srchR25_refutes_0 :
    FamilyRefutes Magma.srchR25 [
      16, 26, 72, 258, 310, 367, 427, 466, 500, 513, 528, 575, 833, 836, 843, 909
    ] :=
  ⟨noSR25_Law16, noSR25_Law26, noSR25_Law72, noSR25_Law258, noSR25_Law310, noSR25_Law367, noSR25_Law427, noSR25_Law466, noSR25_Law500, noSR25_Law513, noSR25_Law528, noSR25_Law575, noSR25_Law833, noSR25_Law836, noSR25_Law843, noSR25_Law909⟩
