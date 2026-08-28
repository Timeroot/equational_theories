import equational_theories.Definability.Srch_S16R324

/-!
# Structural certificate targets: `Magma.srch16R324` (part 3 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S16R324_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 347 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S16R324_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2460 takes them (3 nodes). -/
def ordS16R324_Law2460 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2460. -/
theorem noS16R324_Law2460 : ∀ v : Magma.tup16R324,
    ¬ @Equation2460 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2460) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2460) (by native_decide) v.1 v.2
    ((@Law2460.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2467 takes them (3 nodes). -/
def ordS16R324_Law2467 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2467. -/
theorem noS16R324_Law2467 : ∀ v : Magma.tup16R324,
    ¬ @Equation2467 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2467) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2467) (by native_decide) v.1 v.2
    ((@Law2467.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (3 nodes). -/
def ordS16R324_Law2470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2470. -/
theorem noS16R324_Law2470 : ∀ v : Magma.tup16R324,
    ¬ @Equation2470 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2485 takes them (3 nodes). -/
def ordS16R324_Law2485 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2485. -/
theorem noS16R324_Law2485 : ∀ v : Magma.tup16R324,
    ¬ @Equation2485 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (5 nodes). -/
def ordS16R324_Law2496 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2496. -/
theorem noS16R324_Law2496 : ∀ v : Magma.tup16R324,
    ¬ @Equation2496 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2503 takes them (3 nodes). -/
def ordS16R324_Law2503 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2503. -/
theorem noS16R324_Law2503 : ∀ v : Magma.tup16R324,
    ¬ @Equation2503 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2503) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2503) (by native_decide) v.1 v.2
    ((@Law2503.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2506 takes them (3 nodes). -/
def ordS16R324_Law2506 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2506. -/
theorem noS16R324_Law2506 : ∀ v : Magma.tup16R324,
    ¬ @Equation2506 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2506) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2506) (by native_decide) v.1 v.2
    ((@Law2506.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (5 nodes). -/
def ordS16R324_Law2530 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2530. -/
theorem noS16R324_Law2530 : ∀ v : Magma.tup16R324,
    ¬ @Equation2530 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2533 takes them (3 nodes). -/
def ordS16R324_Law2533 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2533. -/
theorem noS16R324_Law2533 : ∀ v : Magma.tup16R324,
    ¬ @Equation2533 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2533) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2533) (by native_decide) v.1 v.2
    ((@Law2533.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2534 takes them (4 nodes). -/
def ordS16R324_Law2534 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2534. -/
theorem noS16R324_Law2534 : ∀ v : Magma.tup16R324,
    ¬ @Equation2534 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2534) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2534) (by native_decide) v.1 v.2
    ((@Law2534.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2538 takes them (4 nodes). -/
def ordS16R324_Law2538 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2538. -/
theorem noS16R324_Law2538 : ∀ v : Magma.tup16R324,
    ¬ @Equation2538 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2538) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law2538) (by native_decide) v.1 v.2
    ((@Law2538.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2540 takes them (3 nodes). -/
def ordS16R324_Law2540 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2540. -/
theorem noS16R324_Law2540 : ∀ v : Magma.tup16R324,
    ¬ @Equation2540 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2540) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2540) (by native_decide) v.1 v.2
    ((@Law2540.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2647 takes them (5 nodes). -/
def ordS16R324_Law2647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2647. -/
theorem noS16R324_Law2647 : ∀ v : Magma.tup16R324,
    ¬ @Equation2647 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2647) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2647) (by native_decide) v.1 v.2
    ((@Law2647.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2650 takes them (3 nodes). -/
def ordS16R324_Law2650 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2650. -/
theorem noS16R324_Law2650 : ∀ v : Magma.tup16R324,
    ¬ @Equation2650 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2650) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2650) (by native_decide) v.1 v.2
    ((@Law2650.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (3 nodes). -/
def ordS16R324_Law2653 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2653. -/
theorem noS16R324_Law2653 : ∀ v : Magma.tup16R324,
    ¬ @Equation2653 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2660 takes them (3 nodes). -/
def ordS16R324_Law2660 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2660. -/
theorem noS16R324_Law2660 : ∀ v : Magma.tup16R324,
    ¬ @Equation2660 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (3 nodes). -/
def ordS16R324_Law2663 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2663. -/
theorem noS16R324_Law2663 : ∀ v : Magma.tup16R324,
    ¬ @Equation2663 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2672 takes them (4 nodes). -/
def ordS16R324_Law2672 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2672. -/
theorem noS16R324_Law2672 : ∀ v : Magma.tup16R324,
    ¬ @Equation2672 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2672) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2672) (by native_decide) v.1 v.2
    ((@Law2672.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (5 nodes). -/
def ordS16R324_Law2673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2673. -/
theorem noS16R324_Law2673 : ∀ v : Magma.tup16R324,
    ¬ @Equation2673 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (3 nodes). -/
def ordS16R324_Law2699 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2699. -/
theorem noS16R324_Law2699 : ∀ v : Magma.tup16R324,
    ¬ @Equation2699 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2709 takes them (5 nodes). -/
def ordS16R324_Law2709 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2709. -/
theorem noS16R324_Law2709 : ∀ v : Magma.tup16R324,
    ¬ @Equation2709 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2709) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2709) (by native_decide) v.1 v.2
    ((@Law2709.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (5 nodes). -/
def ordS16R324_Law2736 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2736. -/
theorem noS16R324_Law2736 : ∀ v : Magma.tup16R324,
    ¬ @Equation2736 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2743 takes them (3 nodes). -/
def ordS16R324_Law2743 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2743. -/
theorem noS16R324_Law2743 : ∀ v : Magma.tup16R324,
    ¬ @Equation2743 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2743) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2743) (by native_decide) v.1 v.2
    ((@Law2743.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (3 nodes). -/
def ordS16R324_Law2850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2850. -/
theorem noS16R324_Law2850 : ∀ v : Magma.tup16R324,
    ¬ @Equation2850 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2853 takes them (3 nodes). -/
def ordS16R324_Law2853 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2853. -/
theorem noS16R324_Law2853 : ∀ v : Magma.tup16R324,
    ¬ @Equation2853 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2853) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2853) (by native_decide) v.1 v.2
    ((@Law2853.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2855 takes them (6 nodes). -/
def ordS16R324_Law2855 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2855. -/
theorem noS16R324_Law2855 : ∀ v : Magma.tup16R324,
    ¬ @Equation2855 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2855) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2855) (by native_decide) v.1 v.2
    ((@Law2855.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2856 takes them (3 nodes). -/
def ordS16R324_Law2856 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2856. -/
theorem noS16R324_Law2856 : ∀ v : Magma.tup16R324,
    ¬ @Equation2856 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2856) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2856) (by native_decide) v.1 v.2
    ((@Law2856.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2863 takes them (5 nodes). -/
def ordS16R324_Law2863 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2863. -/
theorem noS16R324_Law2863 : ∀ v : Magma.tup16R324,
    ¬ @Equation2863 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2863) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2863) (by native_decide) v.1 v.2
    ((@Law2863.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2865 takes them (4 nodes). -/
def ordS16R324_Law2865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2865. -/
theorem noS16R324_Law2865 : ∀ v : Magma.tup16R324,
    ¬ @Equation2865 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2865) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2865) (by native_decide) v.1 v.2
    ((@Law2865.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2873 takes them (3 nodes). -/
def ordS16R324_Law2873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2873. -/
theorem noS16R324_Law2873 : ∀ v : Magma.tup16R324,
    ¬ @Equation2873 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2873) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2873) (by native_decide) v.1 v.2
    ((@Law2873.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2875 takes them (4 nodes). -/
def ordS16R324_Law2875 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2875. -/
theorem noS16R324_Law2875 : ∀ v : Magma.tup16R324,
    ¬ @Equation2875 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2875) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2875) (by native_decide) v.1 v.2
    ((@Law2875.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (5 nodes). -/
def ordS16R324_Law2876 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2876. -/
theorem noS16R324_Law2876 : ∀ v : Magma.tup16R324,
    ¬ @Equation2876 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2902 takes them (5 nodes). -/
def ordS16R324_Law2902 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2902. -/
theorem noS16R324_Law2902 : ∀ v : Magma.tup16R324,
    ¬ @Equation2902 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2902) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2902) (by native_decide) v.1 v.2
    ((@Law2902.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (5 nodes). -/
def ordS16R324_Law2909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2909. -/
theorem noS16R324_Law2909 : ∀ v : Magma.tup16R324,
    ¬ @Equation2909 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2912 takes them (3 nodes). -/
def ordS16R324_Law2912 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2912. -/
theorem noS16R324_Law2912 : ∀ v : Magma.tup16R324,
    ¬ @Equation2912 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2912) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2912) (by native_decide) v.1 v.2
    ((@Law2912.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2936 takes them (3 nodes). -/
def ordS16R324_Law2936 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2936. -/
theorem noS16R324_Law2936 : ∀ v : Magma.tup16R324,
    ¬ @Equation2936 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2936) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2936) (by native_decide) v.1 v.2
    ((@Law2936.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2939 takes them (3 nodes). -/
def ordS16R324_Law2939 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2939. -/
theorem noS16R324_Law2939 : ∀ v : Magma.tup16R324,
    ¬ @Equation2939 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2939) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2939) (by native_decide) v.1 v.2
    ((@Law2939.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2940 takes them (4 nodes). -/
def ordS16R324_Law2940 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2940. -/
theorem noS16R324_Law2940 : ∀ v : Magma.tup16R324,
    ¬ @Equation2940 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2940) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law2940) (by native_decide) v.1 v.2
    ((@Law2940.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (3 nodes). -/
def ordS16R324_Law3053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3053. -/
theorem noS16R324_Law3053 : ∀ v : Magma.tup16R324,
    ¬ @Equation3053 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (3 nodes). -/
def ordS16R324_Law3056 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3056. -/
theorem noS16R324_Law3056 : ∀ v : Magma.tup16R324,
    ¬ @Equation3056 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3058 takes them (4 nodes). -/
def ordS16R324_Law3058 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3058. -/
theorem noS16R324_Law3058 : ∀ v : Magma.tup16R324,
    ¬ @Equation3058 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3058) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3058) (by native_decide) v.1 v.2
    ((@Law3058.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3059 takes them (5 nodes). -/
def ordS16R324_Law3059 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3059. -/
theorem noS16R324_Law3059 : ∀ v : Magma.tup16R324,
    ¬ @Equation3059 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3059) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3059) (by native_decide) v.1 v.2
    ((@Law3059.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (5 nodes). -/
def ordS16R324_Law3066 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3066. -/
theorem noS16R324_Law3066 : ∀ v : Magma.tup16R324,
    ¬ @Equation3066 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (4 nodes). -/
def ordS16R324_Law3068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3068. -/
theorem noS16R324_Law3068 : ∀ v : Magma.tup16R324,
    ¬ @Equation3068 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3069 takes them (3 nodes). -/
def ordS16R324_Law3069 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3069. -/
theorem noS16R324_Law3069 : ∀ v : Magma.tup16R324,
    ¬ @Equation3069 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3069) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3069) (by native_decide) v.1 v.2
    ((@Law3069.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (4 nodes). -/
def ordS16R324_Law3075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3075. -/
theorem noS16R324_Law3075 : ∀ v : Magma.tup16R324,
    ¬ @Equation3075 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3076 takes them (3 nodes). -/
def ordS16R324_Law3076 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3076. -/
theorem noS16R324_Law3076 : ∀ v : Magma.tup16R324,
    ¬ @Equation3076 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3076) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3076) (by native_decide) v.1 v.2
    ((@Law3076.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (6 nodes). -/
def ordS16R324_Law3078 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3078. -/
theorem noS16R324_Law3078 : ∀ v : Magma.tup16R324,
    ¬ @Equation3078 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (3 nodes). -/
def ordS16R324_Law3079 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3079. -/
theorem noS16R324_Law3079 : ∀ v : Magma.tup16R324,
    ¬ @Equation3079 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (3 nodes). -/
def ordS16R324_Law3083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3083. -/
theorem noS16R324_Law3083 : ∀ v : Magma.tup16R324,
    ¬ @Equation3083 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (3 nodes). -/
def ordS16R324_Law3091 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3091. -/
theorem noS16R324_Law3091 : ∀ v : Magma.tup16R324,
    ¬ @Equation3091 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (3 nodes). -/
def ordS16R324_Law3094 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3094. -/
theorem noS16R324_Law3094 : ∀ v : Magma.tup16R324,
    ¬ @Equation3094 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (3 nodes). -/
def ordS16R324_Law3105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3105. -/
theorem noS16R324_Law3105 : ∀ v : Magma.tup16R324,
    ¬ @Equation3105 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (5 nodes). -/
def ordS16R324_Law3112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3112. -/
theorem noS16R324_Law3112 : ∀ v : Magma.tup16R324,
    ¬ @Equation3112 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3115 takes them (3 nodes). -/
def ordS16R324_Law3115 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3115. -/
theorem noS16R324_Law3115 : ∀ v : Magma.tup16R324,
    ¬ @Equation3115 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3115) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3115) (by native_decide) v.1 v.2
    ((@Law3115.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (5 nodes). -/
def ordS16R324_Law3142 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3142. -/
theorem noS16R324_Law3142 : ∀ v : Magma.tup16R324,
    ¬ @Equation3142 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (5 nodes). -/
def ordS16R324_Law3259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3259. -/
theorem noS16R324_Law3259 : ∀ v : Magma.tup16R324,
    ¬ @Equation3259 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3261 takes them (4 nodes). -/
def ordS16R324_Law3261 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3261. -/
theorem noS16R324_Law3261 : ∀ v : Magma.tup16R324,
    ¬ @Equation3261 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3261) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3261) (by native_decide) v.1 v.2
    ((@Law3261.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3271 takes them (3 nodes). -/
def ordS16R324_Law3271 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3271. -/
theorem noS16R324_Law3271 : ∀ v : Magma.tup16R324,
    ¬ @Equation3271 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3271) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3271) (by native_decide) v.1 v.2
    ((@Law3271.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3272 takes them (4 nodes). -/
def ordS16R324_Law3272 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3272. -/
theorem noS16R324_Law3272 : ∀ v : Magma.tup16R324,
    ¬ @Equation3272 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3272) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3272) (by native_decide) v.1 v.2
    ((@Law3272.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (3 nodes). -/
def ordS16R324_Law3278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3278. -/
theorem noS16R324_Law3278 : ∀ v : Magma.tup16R324,
    ¬ @Equation3278 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3281 takes them (5 nodes). -/
def ordS16R324_Law3281 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3281. -/
theorem noS16R324_Law3281 : ∀ v : Magma.tup16R324,
    ¬ @Equation3281 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3281) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3281) (by native_decide) v.1 v.2
    ((@Law3281.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3306 takes them (4 nodes). -/
def ordS16R324_Law3306 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3306. -/
theorem noS16R324_Law3306 : ∀ v : Magma.tup16R324,
    ¬ @Equation3306 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3306) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3306) (by native_decide) v.1 v.2
    ((@Law3306.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (5 nodes). -/
def ordS16R324_Law3308 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3308. -/
theorem noS16R324_Law3308 : ∀ v : Magma.tup16R324,
    ¬ @Equation3308 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (5 nodes). -/
def ordS16R324_Law3331 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3331. -/
theorem noS16R324_Law3331 : ∀ v : Magma.tup16R324,
    ¬ @Equation3331 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (4 nodes). -/
def ordS16R324_Law3334 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3334. -/
theorem noS16R324_Law3334 : ∀ v : Magma.tup16R324,
    ¬ @Equation3334 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (5 nodes). -/
def ordS16R324_Law3343 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3343. -/
theorem noS16R324_Law3343 : ∀ v : Magma.tup16R324,
    ¬ @Equation3343 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3352 takes them (4 nodes). -/
def ordS16R324_Law3352 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3352. -/
theorem noS16R324_Law3352 : ∀ v : Magma.tup16R324,
    ¬ @Equation3352 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3352) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3352) (by native_decide) v.1 v.2
    ((@Law3352.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3353 takes them (3 nodes). -/
def ordS16R324_Law3353 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3353. -/
theorem noS16R324_Law3353 : ∀ v : Magma.tup16R324,
    ¬ @Equation3353 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3353) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3353) (by native_decide) v.1 v.2
    ((@Law3353.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (3 nodes). -/
def ordS16R324_Law3414 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3414. -/
theorem noS16R324_Law3414 : ∀ v : Magma.tup16R324,
    ¬ @Equation3414 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3459 takes them (3 nodes). -/
def ordS16R324_Law3459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3459. -/
theorem noS16R324_Law3459 : ∀ v : Magma.tup16R324,
    ¬ @Equation3459 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3459) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3459) (by native_decide) v.1 v.2
    ((@Law3459.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (5 nodes). -/
def ordS16R324_Law3462 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3462. -/
theorem noS16R324_Law3462 : ∀ v : Magma.tup16R324,
    ¬ @Equation3462 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3472 takes them (4 nodes). -/
def ordS16R324_Law3472 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3472. -/
theorem noS16R324_Law3472 : ∀ v : Magma.tup16R324,
    ¬ @Equation3472 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3472) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3472) (by native_decide) v.1 v.2
    ((@Law3472.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3474 takes them (3 nodes). -/
def ordS16R324_Law3474 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3474. -/
theorem noS16R324_Law3474 : ∀ v : Magma.tup16R324,
    ¬ @Equation3474 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3474) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3474) (by native_decide) v.1 v.2
    ((@Law3474.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3481 takes them (5 nodes). -/
def ordS16R324_Law3481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3481. -/
theorem noS16R324_Law3481 : ∀ v : Magma.tup16R324,
    ¬ @Equation3481 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (3 nodes). -/
def ordS16R324_Law3484 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3484. -/
theorem noS16R324_Law3484 : ∀ v : Magma.tup16R324,
    ¬ @Equation3484 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (5 nodes). -/
def ordS16R324_Law3511 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3511. -/
theorem noS16R324_Law3511 : ∀ v : Magma.tup16R324,
    ¬ @Equation3511 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3518 takes them (3 nodes). -/
def ordS16R324_Law3518 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3518. -/
theorem noS16R324_Law3518 : ∀ v : Magma.tup16R324,
    ¬ @Equation3518 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3518) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3518) (by native_decide) v.1 v.2
    ((@Law3518.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (3 nodes). -/
def ordS16R324_Law3526 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3526. -/
theorem noS16R324_Law3526 : ∀ v : Magma.tup16R324,
    ¬ @Equation3526 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (5 nodes). -/
def ordS16R324_Law3534 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3534. -/
theorem noS16R324_Law3534 : ∀ v : Magma.tup16R324,
    ¬ @Equation3534 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 3)
    (ord := ordS16R324_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (5 nodes). -/
def ordS16R324_Law3549 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3549. -/
theorem noS16R324_Law3549 : ∀ v : Magma.tup16R324,
    ¬ @Equation3549 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (3 nodes). -/
def ordS16R324_Law3556 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3556. -/
theorem noS16R324_Law3556 : ∀ v : Magma.tup16R324,
    ¬ @Equation3556 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3558 takes them (4 nodes). -/
def ordS16R324_Law3558 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3558. -/
theorem noS16R324_Law3558 : ∀ v : Magma.tup16R324,
    ¬ @Equation3558 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3558) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3558) (by native_decide) v.1 v.2
    ((@Law3558.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3668 takes them (3 nodes). -/
def ordS16R324_Law3668 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3668. -/
theorem noS16R324_Law3668 : ∀ v : Magma.tup16R324,
    ¬ @Equation3668 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3668) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3668) (by native_decide) v.1 v.2
    ((@Law3668.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3678 takes them (4 nodes). -/
def ordS16R324_Law3678 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3678. -/
theorem noS16R324_Law3678 : ∀ v : Magma.tup16R324,
    ¬ @Equation3678 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3678) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3678) (by native_decide) v.1 v.2
    ((@Law3678.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3685 takes them (4 nodes). -/
def ordS16R324_Law3685 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3685. -/
theorem noS16R324_Law3685 : ∀ v : Magma.tup16R324,
    ¬ @Equation3685 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3685) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3685) (by native_decide) v.1 v.2
    ((@Law3685.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3687 takes them (3 nodes). -/
def ordS16R324_Law3687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3687. -/
theorem noS16R324_Law3687 : ∀ v : Magma.tup16R324,
    ¬ @Equation3687 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3687) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3687) (by native_decide) v.1 v.2
    ((@Law3687.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3724 takes them (3 nodes). -/
def ordS16R324_Law3724 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3724. -/
theorem noS16R324_Law3724 : ∀ v : Magma.tup16R324,
    ¬ @Equation3724 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3724) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3724) (by native_decide) v.1 v.2
    ((@Law3724.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3748 takes them (4 nodes). -/
def ordS16R324_Law3748 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3748. -/
theorem noS16R324_Law3748 : ∀ v : Magma.tup16R324,
    ¬ @Equation3748 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3748) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3748) (by native_decide) v.1 v.2
    ((@Law3748.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3749 takes them (3 nodes). -/
def ordS16R324_Law3749 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3749. -/
theorem noS16R324_Law3749 : ∀ v : Magma.tup16R324,
    ¬ @Equation3749 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3749) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3749) (by native_decide) v.1 v.2
    ((@Law3749.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3761 takes them (4 nodes). -/
def ordS16R324_Law3761 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3761. -/
theorem noS16R324_Law3761 : ∀ v : Magma.tup16R324,
    ¬ @Equation3761 (Fin 16) (Magma.srch16R324 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3761) (E := S16R324.E) (tr := S16R324.tr) (z := S16R324.z)
    (st := S16R324.st) (X := S16R324.X) (envs := Magma.envsRed 16 S16R324.E 2)
    (ord := ordS16R324_Law3761) (by native_decide) v.1 v.2
    ((@Law3761.models_iff (Fin 16) (Magma.srch16R324 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch16R324_refutes_2 :
    FamilyRefutes Magma.srch16R324 [
      2460, 2467, 2470, 2485, 2496, 2503, 2506, 2530, 2533, 2534, 2538, 2540, 2647, 2650, 2653,
      2660, 2663, 2672, 2673, 2699, 2709, 2736, 2743, 2850, 2853, 2855, 2856, 2863, 2865, 2873,
      2875, 2876, 2902, 2909, 2912, 2936, 2939, 2940, 3053, 3056, 3058, 3059, 3066, 3068, 3069,
      3075, 3076, 3078, 3079, 3083, 3091, 3094, 3105, 3112, 3115, 3142, 3259, 3261, 3271, 3272,
      3278, 3281, 3306, 3308, 3331, 3334, 3343, 3352, 3353, 3414, 3459, 3462, 3472, 3474, 3481,
      3484, 3511, 3518, 3526, 3534, 3549, 3556, 3558, 3668, 3678, 3685, 3687, 3724, 3748, 3749,
      3761
    ] :=
  ⟨noS16R324_Law2460, noS16R324_Law2467, noS16R324_Law2470, noS16R324_Law2485, noS16R324_Law2496, noS16R324_Law2503, noS16R324_Law2506, noS16R324_Law2530, noS16R324_Law2533, noS16R324_Law2534, noS16R324_Law2538, noS16R324_Law2540, noS16R324_Law2647, noS16R324_Law2650, noS16R324_Law2653, noS16R324_Law2660, noS16R324_Law2663, noS16R324_Law2672, noS16R324_Law2673, noS16R324_Law2699, noS16R324_Law2709, noS16R324_Law2736, noS16R324_Law2743, noS16R324_Law2850, noS16R324_Law2853, noS16R324_Law2855, noS16R324_Law2856, noS16R324_Law2863, noS16R324_Law2865, noS16R324_Law2873, noS16R324_Law2875, noS16R324_Law2876, noS16R324_Law2902, noS16R324_Law2909, noS16R324_Law2912, noS16R324_Law2936, noS16R324_Law2939, noS16R324_Law2940, noS16R324_Law3053, noS16R324_Law3056, noS16R324_Law3058, noS16R324_Law3059, noS16R324_Law3066, noS16R324_Law3068, noS16R324_Law3069, noS16R324_Law3075, noS16R324_Law3076, noS16R324_Law3078, noS16R324_Law3079, noS16R324_Law3083, noS16R324_Law3091, noS16R324_Law3094, noS16R324_Law3105, noS16R324_Law3112, noS16R324_Law3115, noS16R324_Law3142, noS16R324_Law3259, noS16R324_Law3261, noS16R324_Law3271, noS16R324_Law3272, noS16R324_Law3278, noS16R324_Law3281, noS16R324_Law3306, noS16R324_Law3308, noS16R324_Law3331, noS16R324_Law3334, noS16R324_Law3343, noS16R324_Law3352, noS16R324_Law3353, noS16R324_Law3414, noS16R324_Law3459, noS16R324_Law3462, noS16R324_Law3472, noS16R324_Law3474, noS16R324_Law3481, noS16R324_Law3484, noS16R324_Law3511, noS16R324_Law3518, noS16R324_Law3526, noS16R324_Law3534, noS16R324_Law3549, noS16R324_Law3556, noS16R324_Law3558, noS16R324_Law3668, noS16R324_Law3678, noS16R324_Law3685, noS16R324_Law3687, noS16R324_Law3724, noS16R324_Law3748, noS16R324_Law3749, noS16R324_Law3761⟩
