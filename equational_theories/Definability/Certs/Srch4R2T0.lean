import equational_theories.Definability.Srch_S4R2

/-!
# Structural certificate targets: `Magma.srch4R2`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `12`
equations here, 1,168 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 765 takes them (70 nodes). -/
def ordS4R2_Law765 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 765. -/
theorem noS4R2_Law765 : ∀ v : Magma.tup4R2,
    ¬ @Equation765 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law765) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law765) (by native_decide) v.1 v.2
    ((@Law765.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 778 takes them (70 nodes). -/
def ordS4R2_Law778 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 778. -/
theorem noS4R2_Law778 : ∀ v : Magma.tup4R2,
    ¬ @Equation778 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law778) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law778) (by native_decide) v.1 v.2
    ((@Law778.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 934 takes them (73 nodes). -/
def ordS4R2_Law934 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 934. -/
theorem noS4R2_Law934 : ∀ v : Magma.tup4R2,
    ¬ @Equation934 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law934) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law934) (by native_decide) v.1 v.2
    ((@Law934.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 968 takes them (73 nodes). -/
def ordS4R2_Law968 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 968. -/
theorem noS4R2_Law968 : ∀ v : Magma.tup4R2,
    ¬ @Equation968 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law968) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law968) (by native_decide) v.1 v.2
    ((@Law968.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1577 takes them (77 nodes). -/
def ordS4R2_Law1577 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1577. -/
theorem noS4R2_Law1577 : ∀ v : Magma.tup4R2,
    ¬ @Equation1577 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1577) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law1577) (by native_decide) v.1 v.2
    ((@Law1577.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1590 takes them (74 nodes). -/
def ordS4R2_Law1590 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1590. -/
theorem noS4R2_Law1590 : ∀ v : Magma.tup4R2,
    ¬ @Equation1590 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1590) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law1590) (by native_decide) v.1 v.2
    ((@Law1590.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2076 takes them (129 nodes). -/
def ordS4R2_Law2076 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2076. -/
theorem noS4R2_Law2076 : ∀ v : Magma.tup4R2,
    ¬ @Equation2076 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2076) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law2076) (by native_decide) v.1 v.2
    ((@Law2076.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2079 takes them (124 nodes). -/
def ordS4R2_Law2079 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2079. -/
theorem noS4R2_Law2079 : ∀ v : Magma.tup4R2,
    ¬ @Equation2079 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2079) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law2079) (by native_decide) v.1 v.2
    ((@Law2079.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2677 takes them (111 nodes). -/
def ordS4R2_Law2677 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2677. -/
theorem noS4R2_Law2677 : ∀ v : Magma.tup4R2,
    ¬ @Equation2677 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2677) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law2677) (by native_decide) v.1 v.2
    ((@Law2677.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2685 takes them (132 nodes). -/
def ordS4R2_Law2685 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2685. -/
theorem noS4R2_Law2685 : ∀ v : Magma.tup4R2,
    ¬ @Equation2685 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2685) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law2685) (by native_decide) v.1 v.2
    ((@Law2685.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2888 takes them (107 nodes). -/
def ordS4R2_Law2888 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2888. -/
theorem noS4R2_Law2888 : ∀ v : Magma.tup4R2,
    ¬ @Equation2888 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2888) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law2888) (by native_decide) v.1 v.2
    ((@Law2888.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2891 takes them (128 nodes). -/
def ordS4R2_Law2891 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2891. -/
theorem noS4R2_Law2891 : ∀ v : Magma.tup4R2,
    ¬ @Equation2891 (Fin 4) (Magma.srch4R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2891) (E := S4R2.E) (tr := S4R2.tr) (z := S4R2.z)
    (st := S4R2.st) (X := S4R2.X) (envs := Magma.envsRed 4 S4R2.E 3)
    (ord := ordS4R2_Law2891) (by native_decide) v.1 v.2
    ((@Law2891.models_iff (Fin 4) (Magma.srch4R2 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch4R2_refutes_0 :
    FamilyRefutes Magma.srch4R2 [
      765, 778, 934, 968, 1577, 1590, 2076, 2079, 2677, 2685, 2888, 2891
    ] :=
  ⟨noS4R2_Law765, noS4R2_Law778, noS4R2_Law934, noS4R2_Law968, noS4R2_Law1577, noS4R2_Law1590, noS4R2_Law2076, noS4R2_Law2079, noS4R2_Law2677, noS4R2_Law2685, noS4R2_Law2888, noS4R2_Law2891⟩
