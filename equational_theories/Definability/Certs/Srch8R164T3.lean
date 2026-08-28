import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 4 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `77` equations here, 897 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2533 takes them (11 nodes). -/
def ordS8R164_Law2533 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2533. -/
theorem noS8R164_Law2533 : ∀ v : Magma.tup8R164,
    ¬ @Equation2533 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2533) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2533) (by native_decide) v.1 v.2
    ((@Law2533.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2536 takes them (9 nodes). -/
def ordS8R164_Law2536 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2536. -/
theorem noS8R164_Law2536 : ∀ v : Magma.tup8R164,
    ¬ @Equation2536 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2536) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2536) (by native_decide) v.1 v.2
    ((@Law2536.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2554 takes them (10 nodes). -/
def ordS8R164_Law2554 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2554. -/
theorem noS8R164_Law2554 : ∀ v : Magma.tup8R164,
    ¬ @Equation2554 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2554) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2554) (by native_decide) v.1 v.2
    ((@Law2554.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2571 takes them (9 nodes). -/
def ordS8R164_Law2571 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2571. -/
theorem noS8R164_Law2571 : ∀ v : Magma.tup8R164,
    ¬ @Equation2571 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2571) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2571) (by native_decide) v.1 v.2
    ((@Law2571.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2588 takes them (9 nodes). -/
def ordS8R164_Law2588 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2588. -/
theorem noS8R164_Law2588 : ∀ v : Magma.tup8R164,
    ¬ @Equation2588 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2588) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2588) (by native_decide) v.1 v.2
    ((@Law2588.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2623 takes them (9 nodes). -/
def ordS8R164_Law2623 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2623. -/
theorem noS8R164_Law2623 : ∀ v : Magma.tup8R164,
    ¬ @Equation2623 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2623) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2623) (by native_decide) v.1 v.2
    ((@Law2623.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2646 takes them (18 nodes). -/
def ordS8R164_Law2646 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2646. -/
theorem noS8R164_Law2646 : ∀ v : Magma.tup8R164,
    ¬ @Equation2646 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2646) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2646) (by native_decide) v.1 v.2
    ((@Law2646.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2665 takes them (16 nodes). -/
def ordS8R164_Law2665 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2665. -/
theorem noS8R164_Law2665 : ∀ v : Magma.tup8R164,
    ¬ @Equation2665 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2665) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2665) (by native_decide) v.1 v.2
    ((@Law2665.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2702 takes them (11 nodes). -/
def ordS8R164_Law2702 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2702. -/
theorem noS8R164_Law2702 : ∀ v : Magma.tup8R164,
    ¬ @Equation2702 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2702) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2702) (by native_decide) v.1 v.2
    ((@Law2702.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2712 takes them (9 nodes). -/
def ordS8R164_Law2712 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2712. -/
theorem noS8R164_Law2712 : ∀ v : Magma.tup8R164,
    ¬ @Equation2712 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2712) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2712) (by native_decide) v.1 v.2
    ((@Law2712.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2739 takes them (11 nodes). -/
def ordS8R164_Law2739 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2739. -/
theorem noS8R164_Law2739 : ∀ v : Magma.tup8R164,
    ¬ @Equation2739 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2739) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2739) (by native_decide) v.1 v.2
    ((@Law2739.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2774 takes them (11 nodes). -/
def ordS8R164_Law2774 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2774. -/
theorem noS8R164_Law2774 : ∀ v : Magma.tup8R164,
    ¬ @Equation2774 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2774) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2774) (by native_decide) v.1 v.2
    ((@Law2774.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (11 nodes). -/
def ordS8R164_Law2778 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2778. -/
theorem noS8R164_Law2778 : ∀ v : Magma.tup8R164,
    ¬ @Equation2778 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2782 takes them (11 nodes). -/
def ordS8R164_Law2782 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2782. -/
theorem noS8R164_Law2782 : ∀ v : Magma.tup8R164,
    ¬ @Equation2782 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2782) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2782) (by native_decide) v.1 v.2
    ((@Law2782.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3052 takes them (17 nodes). -/
def ordS8R164_Law3052 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3052. -/
theorem noS8R164_Law3052 : ∀ v : Magma.tup8R164,
    ¬ @Equation3052 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3052) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3052) (by native_decide) v.1 v.2
    ((@Law3052.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3065 takes them (16 nodes). -/
def ordS8R164_Law3065 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3065. -/
theorem noS8R164_Law3065 : ∀ v : Magma.tup8R164,
    ¬ @Equation3065 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3065) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3065) (by native_decide) v.1 v.2
    ((@Law3065.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3071 takes them (16 nodes). -/
def ordS8R164_Law3071 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3071. -/
theorem noS8R164_Law3071 : ∀ v : Magma.tup8R164,
    ¬ @Equation3071 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3071) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3071) (by native_decide) v.1 v.2
    ((@Law3071.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (16 nodes). -/
def ordS8R164_Law3078 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3078. -/
theorem noS8R164_Law3078 : ∀ v : Magma.tup8R164,
    ¬ @Equation3078 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3093 takes them (14 nodes). -/
def ordS8R164_Law3093 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3093. -/
theorem noS8R164_Law3093 : ∀ v : Magma.tup8R164,
    ¬ @Equation3093 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3093) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3093) (by native_decide) v.1 v.2
    ((@Law3093.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3115 takes them (10 nodes). -/
def ordS8R164_Law3115 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3115. -/
theorem noS8R164_Law3115 : ∀ v : Magma.tup8R164,
    ¬ @Equation3115 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3115) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3115) (by native_decide) v.1 v.2
    ((@Law3115.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3145 takes them (9 nodes). -/
def ordS8R164_Law3145 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3145. -/
theorem noS8R164_Law3145 : ∀ v : Magma.tup8R164,
    ¬ @Equation3145 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3145) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3145) (by native_decide) v.1 v.2
    ((@Law3145.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3180 takes them (9 nodes). -/
def ordS8R164_Law3180 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3180. -/
theorem noS8R164_Law3180 : ∀ v : Magma.tup8R164,
    ¬ @Equation3180 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3180) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3180) (by native_decide) v.1 v.2
    ((@Law3180.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3197 takes them (9 nodes). -/
def ordS8R164_Law3197 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3197. -/
theorem noS8R164_Law3197 : ∀ v : Magma.tup8R164,
    ¬ @Equation3197 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3197) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3197) (by native_decide) v.1 v.2
    ((@Law3197.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3254 takes them (11 nodes). -/
def ordS8R164_Law3254 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3254. -/
theorem noS8R164_Law3254 : ∀ v : Magma.tup8R164,
    ¬ @Equation3254 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3254) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3254) (by native_decide) v.1 v.2
    ((@Law3254.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3255 takes them (25 nodes). -/
def ordS8R164_Law3255 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3255. -/
theorem noS8R164_Law3255 : ∀ v : Magma.tup8R164,
    ¬ @Equation3255 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3255) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3255) (by native_decide) v.1 v.2
    ((@Law3255.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3257 takes them (11 nodes). -/
def ordS8R164_Law3257 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3257. -/
theorem noS8R164_Law3257 : ∀ v : Magma.tup8R164,
    ¬ @Equation3257 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3257) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3257) (by native_decide) v.1 v.2
    ((@Law3257.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3260 takes them (9 nodes). -/
def ordS8R164_Law3260 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3260. -/
theorem noS8R164_Law3260 : ∀ v : Magma.tup8R164,
    ¬ @Equation3260 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3260) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3260) (by native_decide) v.1 v.2
    ((@Law3260.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3263 takes them (10 nodes). -/
def ordS8R164_Law3263 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3263. -/
theorem noS8R164_Law3263 : ∀ v : Magma.tup8R164,
    ¬ @Equation3263 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3263) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3263) (by native_decide) v.1 v.2
    ((@Law3263.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3264 takes them (18 nodes). -/
def ordS8R164_Law3264 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3264. -/
theorem noS8R164_Law3264 : ∀ v : Magma.tup8R164,
    ¬ @Equation3264 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3264) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3264) (by native_decide) v.1 v.2
    ((@Law3264.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3265 takes them (15 nodes). -/
def ordS8R164_Law3265 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3265. -/
theorem noS8R164_Law3265 : ∀ v : Magma.tup8R164,
    ¬ @Equation3265 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3265) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3265) (by native_decide) v.1 v.2
    ((@Law3265.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3267 takes them (9 nodes). -/
def ordS8R164_Law3267 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3267. -/
theorem noS8R164_Law3267 : ∀ v : Magma.tup8R164,
    ¬ @Equation3267 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3267) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3267) (by native_decide) v.1 v.2
    ((@Law3267.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3270 takes them (7 nodes). -/
def ordS8R164_Law3270 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3270. -/
theorem noS8R164_Law3270 : ∀ v : Magma.tup8R164,
    ¬ @Equation3270 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3270) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3270) (by native_decide) v.1 v.2
    ((@Law3270.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3273 takes them (6 nodes). -/
def ordS8R164_Law3273 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3273. -/
theorem noS8R164_Law3273 : ∀ v : Magma.tup8R164,
    ¬ @Equation3273 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3273) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3273) (by native_decide) v.1 v.2
    ((@Law3273.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3274 takes them (14 nodes). -/
def ordS8R164_Law3274 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3274. -/
theorem noS8R164_Law3274 : ∀ v : Magma.tup8R164,
    ¬ @Equation3274 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3274) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3274) (by native_decide) v.1 v.2
    ((@Law3274.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3275 takes them (12 nodes). -/
def ordS8R164_Law3275 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3275. -/
theorem noS8R164_Law3275 : ∀ v : Magma.tup8R164,
    ¬ @Equation3275 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3275) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3275) (by native_decide) v.1 v.2
    ((@Law3275.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3277 takes them (6 nodes). -/
def ordS8R164_Law3277 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3277. -/
theorem noS8R164_Law3277 : ∀ v : Magma.tup8R164,
    ¬ @Equation3277 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3277) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3277) (by native_decide) v.1 v.2
    ((@Law3277.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3279 takes them (19 nodes). -/
def ordS8R164_Law3279 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3279. -/
theorem noS8R164_Law3279 : ∀ v : Magma.tup8R164,
    ¬ @Equation3279 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3279) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3279) (by native_decide) v.1 v.2
    ((@Law3279.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3280 takes them (8 nodes). -/
def ordS8R164_Law3280 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3280. -/
theorem noS8R164_Law3280 : ∀ v : Magma.tup8R164,
    ¬ @Equation3280 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3280) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3280) (by native_decide) v.1 v.2
    ((@Law3280.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3281 takes them (13 nodes). -/
def ordS8R164_Law3281 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3281. -/
theorem noS8R164_Law3281 : ∀ v : Magma.tup8R164,
    ¬ @Equation3281 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3281) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3281) (by native_decide) v.1 v.2
    ((@Law3281.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3283 takes them (8 nodes). -/
def ordS8R164_Law3283 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3283. -/
theorem noS8R164_Law3283 : ∀ v : Magma.tup8R164,
    ¬ @Equation3283 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3283) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3283) (by native_decide) v.1 v.2
    ((@Law3283.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3284 takes them (12 nodes). -/
def ordS8R164_Law3284 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3284. -/
theorem noS8R164_Law3284 : ∀ v : Magma.tup8R164,
    ¬ @Equation3284 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3284) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3284) (by native_decide) v.1 v.2
    ((@Law3284.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3285 takes them (18 nodes). -/
def ordS8R164_Law3285 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3285. -/
theorem noS8R164_Law3285 : ∀ v : Magma.tup8R164,
    ¬ @Equation3285 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3285) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3285) (by native_decide) v.1 v.2
    ((@Law3285.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3287 takes them (8 nodes). -/
def ordS8R164_Law3287 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3287. -/
theorem noS8R164_Law3287 : ∀ v : Magma.tup8R164,
    ¬ @Equation3287 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3287) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3287) (by native_decide) v.1 v.2
    ((@Law3287.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3289 takes them (12 nodes). -/
def ordS8R164_Law3289 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3289. -/
theorem noS8R164_Law3289 : ∀ v : Magma.tup8R164,
    ¬ @Equation3289 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3289) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3289) (by native_decide) v.1 v.2
    ((@Law3289.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3290 takes them (12 nodes). -/
def ordS8R164_Law3290 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3290. -/
theorem noS8R164_Law3290 : ∀ v : Magma.tup8R164,
    ¬ @Equation3290 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3290) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3290) (by native_decide) v.1 v.2
    ((@Law3290.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3291 takes them (6 nodes). -/
def ordS8R164_Law3291 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3291. -/
theorem noS8R164_Law3291 : ∀ v : Magma.tup8R164,
    ¬ @Equation3291 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3291) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3291) (by native_decide) v.1 v.2
    ((@Law3291.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3292 takes them (10 nodes). -/
def ordS8R164_Law3292 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3292. -/
theorem noS8R164_Law3292 : ∀ v : Magma.tup8R164,
    ¬ @Equation3292 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3292) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3292) (by native_decide) v.1 v.2
    ((@Law3292.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3295 takes them (6 nodes). -/
def ordS8R164_Law3295 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3295. -/
theorem noS8R164_Law3295 : ∀ v : Magma.tup8R164,
    ¬ @Equation3295 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3295) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3295) (by native_decide) v.1 v.2
    ((@Law3295.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3296 takes them (11 nodes). -/
def ordS8R164_Law3296 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3296. -/
theorem noS8R164_Law3296 : ∀ v : Magma.tup8R164,
    ¬ @Equation3296 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3296) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3296) (by native_decide) v.1 v.2
    ((@Law3296.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3299 takes them (7 nodes). -/
def ordS8R164_Law3299 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3299. -/
theorem noS8R164_Law3299 : ∀ v : Magma.tup8R164,
    ¬ @Equation3299 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3299) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3299) (by native_decide) v.1 v.2
    ((@Law3299.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3300 takes them (10 nodes). -/
def ordS8R164_Law3300 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3300. -/
theorem noS8R164_Law3300 : ∀ v : Magma.tup8R164,
    ¬ @Equation3300 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3300) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3300) (by native_decide) v.1 v.2
    ((@Law3300.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3301 takes them (12 nodes). -/
def ordS8R164_Law3301 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3301. -/
theorem noS8R164_Law3301 : ∀ v : Magma.tup8R164,
    ¬ @Equation3301 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3301) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3301) (by native_decide) v.1 v.2
    ((@Law3301.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3302 takes them (12 nodes). -/
def ordS8R164_Law3302 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3302. -/
theorem noS8R164_Law3302 : ∀ v : Magma.tup8R164,
    ¬ @Equation3302 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3302) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3302) (by native_decide) v.1 v.2
    ((@Law3302.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3304 takes them (6 nodes). -/
def ordS8R164_Law3304 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3304. -/
theorem noS8R164_Law3304 : ∀ v : Magma.tup8R164,
    ¬ @Equation3304 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3304) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3304) (by native_decide) v.1 v.2
    ((@Law3304.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3305 takes them (9 nodes). -/
def ordS8R164_Law3305 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3305. -/
theorem noS8R164_Law3305 : ∀ v : Magma.tup8R164,
    ¬ @Equation3305 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3305) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3305) (by native_decide) v.1 v.2
    ((@Law3305.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3307 takes them (9 nodes). -/
def ordS8R164_Law3307 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3307. -/
theorem noS8R164_Law3307 : ∀ v : Magma.tup8R164,
    ¬ @Equation3307 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3307) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3307) (by native_decide) v.1 v.2
    ((@Law3307.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3309 takes them (24 nodes). -/
def ordS8R164_Law3309 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3309. -/
theorem noS8R164_Law3309 : ∀ v : Magma.tup8R164,
    ¬ @Equation3309 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3309) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3309) (by native_decide) v.1 v.2
    ((@Law3309.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3310 takes them (9 nodes). -/
def ordS8R164_Law3310 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3310. -/
theorem noS8R164_Law3310 : ∀ v : Magma.tup8R164,
    ¬ @Equation3310 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3310) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3310) (by native_decide) v.1 v.2
    ((@Law3310.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3311 takes them (9 nodes). -/
def ordS8R164_Law3311 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3311. -/
theorem noS8R164_Law3311 : ∀ v : Magma.tup8R164,
    ¬ @Equation3311 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3311) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3311) (by native_decide) v.1 v.2
    ((@Law3311.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3312 takes them (13 nodes). -/
def ordS8R164_Law3312 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3312. -/
theorem noS8R164_Law3312 : ∀ v : Magma.tup8R164,
    ¬ @Equation3312 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3312) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3312) (by native_decide) v.1 v.2
    ((@Law3312.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3313 takes them (9 nodes). -/
def ordS8R164_Law3313 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3313. -/
theorem noS8R164_Law3313 : ∀ v : Magma.tup8R164,
    ¬ @Equation3313 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3313) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3313) (by native_decide) v.1 v.2
    ((@Law3313.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3314 takes them (9 nodes). -/
def ordS8R164_Law3314 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3314. -/
theorem noS8R164_Law3314 : ∀ v : Magma.tup8R164,
    ¬ @Equation3314 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3314) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3314) (by native_decide) v.1 v.2
    ((@Law3314.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3316 takes them (30 nodes). -/
def ordS8R164_Law3316 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3316. -/
theorem noS8R164_Law3316 : ∀ v : Magma.tup8R164,
    ¬ @Equation3316 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3316) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3316) (by native_decide) v.1 v.2
    ((@Law3316.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3317 takes them (9 nodes). -/
def ordS8R164_Law3317 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3317. -/
theorem noS8R164_Law3317 : ∀ v : Magma.tup8R164,
    ¬ @Equation3317 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3317) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3317) (by native_decide) v.1 v.2
    ((@Law3317.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3318 takes them (21 nodes). -/
def ordS8R164_Law3318 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3318. -/
theorem noS8R164_Law3318 : ∀ v : Magma.tup8R164,
    ¬ @Equation3318 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3318) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law3318) (by native_decide) v.1 v.2
    ((@Law3318.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3320 takes them (10 nodes). -/
def ordS8R164_Law3320 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3320. -/
theorem noS8R164_Law3320 : ∀ v : Magma.tup8R164,
    ¬ @Equation3320 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3320) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3320) (by native_decide) v.1 v.2
    ((@Law3320.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3321 takes them (13 nodes). -/
def ordS8R164_Law3321 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3321. -/
theorem noS8R164_Law3321 : ∀ v : Magma.tup8R164,
    ¬ @Equation3321 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3322 takes them (19 nodes). -/
def ordS8R164_Law3322 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3322. -/
theorem noS8R164_Law3322 : ∀ v : Magma.tup8R164,
    ¬ @Equation3322 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3322) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3322) (by native_decide) v.1 v.2
    ((@Law3322.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (9 nodes). -/
def ordS8R164_Law3324 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3324. -/
theorem noS8R164_Law3324 : ∀ v : Magma.tup8R164,
    ¬ @Equation3324 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3325 takes them (9 nodes). -/
def ordS8R164_Law3325 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3325. -/
theorem noS8R164_Law3325 : ∀ v : Magma.tup8R164,
    ¬ @Equation3325 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3325) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3325) (by native_decide) v.1 v.2
    ((@Law3325.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3326 takes them (13 nodes). -/
def ordS8R164_Law3326 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3326. -/
theorem noS8R164_Law3326 : ∀ v : Magma.tup8R164,
    ¬ @Equation3326 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3326) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3326) (by native_decide) v.1 v.2
    ((@Law3326.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3327 takes them (9 nodes). -/
def ordS8R164_Law3327 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3327. -/
theorem noS8R164_Law3327 : ∀ v : Magma.tup8R164,
    ¬ @Equation3327 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3327) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3327) (by native_decide) v.1 v.2
    ((@Law3327.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3328 takes them (9 nodes). -/
def ordS8R164_Law3328 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3328. -/
theorem noS8R164_Law3328 : ∀ v : Magma.tup8R164,
    ¬ @Equation3328 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3328) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3328) (by native_decide) v.1 v.2
    ((@Law3328.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3329 takes them (10 nodes). -/
def ordS8R164_Law3329 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3329. -/
theorem noS8R164_Law3329 : ∀ v : Magma.tup8R164,
    ¬ @Equation3329 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3329) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3329) (by native_decide) v.1 v.2
    ((@Law3329.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3330 takes them (13 nodes). -/
def ordS8R164_Law3330 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3330. -/
theorem noS8R164_Law3330 : ∀ v : Magma.tup8R164,
    ¬ @Equation3330 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3330) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3330) (by native_decide) v.1 v.2
    ((@Law3330.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3332 takes them (9 nodes). -/
def ordS8R164_Law3332 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3332. -/
theorem noS8R164_Law3332 : ∀ v : Magma.tup8R164,
    ¬ @Equation3332 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3332) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3332) (by native_decide) v.1 v.2
    ((@Law3332.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3333 takes them (9 nodes). -/
def ordS8R164_Law3333 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3333. -/
theorem noS8R164_Law3333 : ∀ v : Magma.tup8R164,
    ¬ @Equation3333 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3333) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3333) (by native_decide) v.1 v.2
    ((@Law3333.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `77` equations. -/
theorem srch8R164_refutes_3 :
    FamilyRefutes Magma.srch8R164 [
      2533, 2536, 2554, 2571, 2588, 2623, 2646, 2665, 2702, 2712, 2739, 2774, 2778, 2782, 3052,
      3065, 3071, 3078, 3093, 3115, 3145, 3180, 3197, 3254, 3255, 3257, 3260, 3263, 3264, 3265,
      3267, 3270, 3273, 3274, 3275, 3277, 3279, 3280, 3281, 3283, 3284, 3285, 3287, 3289, 3290,
      3291, 3292, 3295, 3296, 3299, 3300, 3301, 3302, 3304, 3305, 3307, 3309, 3310, 3311, 3312,
      3313, 3314, 3316, 3317, 3318, 3320, 3321, 3322, 3324, 3325, 3326, 3327, 3328, 3329, 3330,
      3332, 3333
    ] :=
  ⟨noS8R164_Law2533, noS8R164_Law2536, noS8R164_Law2554, noS8R164_Law2571, noS8R164_Law2588, noS8R164_Law2623, noS8R164_Law2646, noS8R164_Law2665, noS8R164_Law2702, noS8R164_Law2712, noS8R164_Law2739, noS8R164_Law2774, noS8R164_Law2778, noS8R164_Law2782, noS8R164_Law3052, noS8R164_Law3065, noS8R164_Law3071, noS8R164_Law3078, noS8R164_Law3093, noS8R164_Law3115, noS8R164_Law3145, noS8R164_Law3180, noS8R164_Law3197, noS8R164_Law3254, noS8R164_Law3255, noS8R164_Law3257, noS8R164_Law3260, noS8R164_Law3263, noS8R164_Law3264, noS8R164_Law3265, noS8R164_Law3267, noS8R164_Law3270, noS8R164_Law3273, noS8R164_Law3274, noS8R164_Law3275, noS8R164_Law3277, noS8R164_Law3279, noS8R164_Law3280, noS8R164_Law3281, noS8R164_Law3283, noS8R164_Law3284, noS8R164_Law3285, noS8R164_Law3287, noS8R164_Law3289, noS8R164_Law3290, noS8R164_Law3291, noS8R164_Law3292, noS8R164_Law3295, noS8R164_Law3296, noS8R164_Law3299, noS8R164_Law3300, noS8R164_Law3301, noS8R164_Law3302, noS8R164_Law3304, noS8R164_Law3305, noS8R164_Law3307, noS8R164_Law3309, noS8R164_Law3310, noS8R164_Law3311, noS8R164_Law3312, noS8R164_Law3313, noS8R164_Law3314, noS8R164_Law3316, noS8R164_Law3317, noS8R164_Law3318, noS8R164_Law3320, noS8R164_Law3321, noS8R164_Law3322, noS8R164_Law3324, noS8R164_Law3325, noS8R164_Law3326, noS8R164_Law3327, noS8R164_Law3328, noS8R164_Law3329, noS8R164_Law3330, noS8R164_Law3332, noS8R164_Law3333⟩
