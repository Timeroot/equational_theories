import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 26 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,760 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2444 takes them (674 nodes). -/
def ordS7R12_Law2444 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2444. -/
theorem noS7R12_Law2444 : ∀ v : Magma.tup7R12,
    ¬ @Equation2444 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2446 takes them (856 nodes). -/
def ordS7R12_Law2446 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2446. -/
theorem noS7R12_Law2446 : ∀ v : Magma.tup7R12,
    ¬ @Equation2446 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2446) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2446) (by native_decide) v.1 v.2
    ((@Law2446.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2452 takes them (408 nodes). -/
def ordS7R12_Law2452 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2452. -/
theorem noS7R12_Law2452 : ∀ v : Magma.tup7R12,
    ¬ @Equation2452 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2452) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2452) (by native_decide) v.1 v.2
    ((@Law2452.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (626 nodes). -/
def ordS7R12_Law2457 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2457. -/
theorem noS7R12_Law2457 : ∀ v : Magma.tup7R12,
    ¬ @Equation2457 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2462 takes them (312 nodes). -/
def ordS7R12_Law2462 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2462. -/
theorem noS7R12_Law2462 : ∀ v : Magma.tup7R12,
    ¬ @Equation2462 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2462) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2462) (by native_decide) v.1 v.2
    ((@Law2462.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (884 nodes). -/
def ordS7R12_Law2470 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2470. -/
theorem noS7R12_Law2470 : ∀ v : Magma.tup7R12,
    ¬ @Equation2470 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R12_refutes_25 :
    FamilyRefutes Magma.srch7R12 [
      2444, 2446, 2452, 2457, 2462, 2470
    ] :=
  ⟨noS7R12_Law2444, noS7R12_Law2446, noS7R12_Law2452, noS7R12_Law2457, noS7R12_Law2462, noS7R12_Law2470⟩
