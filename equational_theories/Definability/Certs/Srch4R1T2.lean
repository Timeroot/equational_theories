import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 3 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,032 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1112 takes them (1247 nodes). -/
def ordS4R1_Law1112 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1112. -/
theorem noS4R1_Law1112 : ∀ v : Magma.tup4R1,
    ¬ @Equation1112 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1112) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1112) (by native_decide) v.1 v.2
    ((@Law1112.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1119 takes them (528 nodes). -/
def ordS4R1_Law1119 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1119. -/
theorem noS4R1_Law1119 : ∀ v : Magma.tup4R1,
    ¬ @Equation1119 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1119) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1119) (by native_decide) v.1 v.2
    ((@Law1119.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1133 takes them (249 nodes). -/
def ordS4R1_Law1133 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1133. -/
theorem noS4R1_Law1133 : ∀ v : Magma.tup4R1,
    ¬ @Equation1133 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1133) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1133) (by native_decide) v.1 v.2
    ((@Law1133.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1150 takes them (369 nodes). -/
def ordS4R1_Law1150 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1150. -/
theorem noS4R1_Law1150 : ∀ v : Magma.tup4R1,
    ¬ @Equation1150 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1150) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1150) (by native_decide) v.1 v.2
    ((@Law1150.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1167 takes them (185 nodes). -/
def ordS4R1_Law1167 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1167. -/
theorem noS4R1_Law1167 : ∀ v : Magma.tup4R1,
    ¬ @Equation1167 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1167) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1167) (by native_decide) v.1 v.2
    ((@Law1167.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1202 takes them (153 nodes). -/
def ordS4R1_Law1202 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1202. -/
theorem noS4R1_Law1202 : ∀ v : Magma.tup4R1,
    ¬ @Equation1202 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1202) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law1202) (by native_decide) v.1 v.2
    ((@Law1202.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1299 takes them (301 nodes). -/
def ordS4R1_Law1299 : List (Fin 8) := [1, 0, 3, 4, 5, 2, 7, 6]

/-- No member of the class satisfies equation 1299. -/
theorem noS4R1_Law1299 : ∀ v : Magma.tup4R1,
    ¬ @Equation1299 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1299) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1299) (by native_decide) v.1 v.2
    ((@Law1299.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch4R1_refutes_2 :
    FamilyRefutes Magma.srch4R1 [
      1112, 1119, 1133, 1150, 1167, 1202, 1299
    ] :=
  ⟨noS4R1_Law1112, noS4R1_Law1119, noS4R1_Law1133, noS4R1_Law1150, noS4R1_Law1167, noS4R1_Law1202, noS4R1_Law1299⟩
