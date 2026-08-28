import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 17 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `80` equations here, 757 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4572 takes them (6 nodes). -/
def ordS8R164_Law4572 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4572. -/
theorem noS8R164_Law4572 : ∀ v : Magma.tup8R164,
    ¬ @Equation4572 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4572) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4572) (by native_decide) v.1 v.2
    ((@Law4572.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4573 takes them (6 nodes). -/
def ordS8R164_Law4573 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4573. -/
theorem noS8R164_Law4573 : ∀ v : Magma.tup8R164,
    ¬ @Equation4573 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4573) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4573) (by native_decide) v.1 v.2
    ((@Law4573.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4574 takes them (10 nodes). -/
def ordS8R164_Law4574 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4574. -/
theorem noS8R164_Law4574 : ∀ v : Magma.tup8R164,
    ¬ @Equation4574 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4574) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4574) (by native_decide) v.1 v.2
    ((@Law4574.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4575 takes them (6 nodes). -/
def ordS8R164_Law4575 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4575. -/
theorem noS8R164_Law4575 : ∀ v : Magma.tup8R164,
    ¬ @Equation4575 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4575) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4575) (by native_decide) v.1 v.2
    ((@Law4575.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4576 takes them (6 nodes). -/
def ordS8R164_Law4576 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4576. -/
theorem noS8R164_Law4576 : ∀ v : Magma.tup8R164,
    ¬ @Equation4576 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4576) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4576) (by native_decide) v.1 v.2
    ((@Law4576.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4577 takes them (6 nodes). -/
def ordS8R164_Law4577 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4577. -/
theorem noS8R164_Law4577 : ∀ v : Magma.tup8R164,
    ¬ @Equation4577 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4577) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4577) (by native_decide) v.1 v.2
    ((@Law4577.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4578 takes them (6 nodes). -/
def ordS8R164_Law4578 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4578. -/
theorem noS8R164_Law4578 : ∀ v : Magma.tup8R164,
    ¬ @Equation4578 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4578) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4578) (by native_decide) v.1 v.2
    ((@Law4578.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4579 takes them (10 nodes). -/
def ordS8R164_Law4579 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4579. -/
theorem noS8R164_Law4579 : ∀ v : Magma.tup8R164,
    ¬ @Equation4579 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4579) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4579) (by native_decide) v.1 v.2
    ((@Law4579.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4580 takes them (6 nodes). -/
def ordS8R164_Law4580 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4580. -/
theorem noS8R164_Law4580 : ∀ v : Magma.tup8R164,
    ¬ @Equation4580 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4580) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4580) (by native_decide) v.1 v.2
    ((@Law4580.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4581 takes them (6 nodes). -/
def ordS8R164_Law4581 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4581. -/
theorem noS8R164_Law4581 : ∀ v : Magma.tup8R164,
    ¬ @Equation4581 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4581) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4581) (by native_decide) v.1 v.2
    ((@Law4581.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4582 takes them (6 nodes). -/
def ordS8R164_Law4582 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4582. -/
theorem noS8R164_Law4582 : ∀ v : Magma.tup8R164,
    ¬ @Equation4582 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4582) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law4582) (by native_decide) v.1 v.2
    ((@Law4582.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4584 takes them (23 nodes). -/
def ordS8R164_Law4584 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4584. -/
theorem noS8R164_Law4584 : ∀ v : Magma.tup8R164,
    ¬ @Equation4584 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4584) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4584) (by native_decide) v.1 v.2
    ((@Law4584.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4586 takes them (9 nodes). -/
def ordS8R164_Law4586 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4586. -/
theorem noS8R164_Law4586 : ∀ v : Magma.tup8R164,
    ¬ @Equation4586 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4586) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4586) (by native_decide) v.1 v.2
    ((@Law4586.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4587 takes them (12 nodes). -/
def ordS8R164_Law4587 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4587. -/
theorem noS8R164_Law4587 : ∀ v : Magma.tup8R164,
    ¬ @Equation4587 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4587) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4587) (by native_decide) v.1 v.2
    ((@Law4587.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4589 takes them (6 nodes). -/
def ordS8R164_Law4589 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4589. -/
theorem noS8R164_Law4589 : ∀ v : Magma.tup8R164,
    ¬ @Equation4589 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4589) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4589) (by native_decide) v.1 v.2
    ((@Law4589.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4593 takes them (10 nodes). -/
def ordS8R164_Law4593 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4593. -/
theorem noS8R164_Law4593 : ∀ v : Magma.tup8R164,
    ¬ @Equation4593 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4593) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4593) (by native_decide) v.1 v.2
    ((@Law4593.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4594 takes them (12 nodes). -/
def ordS8R164_Law4594 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4594. -/
theorem noS8R164_Law4594 : ∀ v : Magma.tup8R164,
    ¬ @Equation4594 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4594) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4594) (by native_decide) v.1 v.2
    ((@Law4594.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4595 takes them (9 nodes). -/
def ordS8R164_Law4595 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4595. -/
theorem noS8R164_Law4595 : ∀ v : Magma.tup8R164,
    ¬ @Equation4595 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4595) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4595) (by native_decide) v.1 v.2
    ((@Law4595.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4596 takes them (6 nodes). -/
def ordS8R164_Law4596 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4596. -/
theorem noS8R164_Law4596 : ∀ v : Magma.tup8R164,
    ¬ @Equation4596 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4596) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4596) (by native_decide) v.1 v.2
    ((@Law4596.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4599 takes them (25 nodes). -/
def ordS8R164_Law4599 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4599. -/
theorem noS8R164_Law4599 : ∀ v : Magma.tup8R164,
    ¬ @Equation4599 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4599) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4599) (by native_decide) v.1 v.2
    ((@Law4599.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4600 takes them (9 nodes). -/
def ordS8R164_Law4600 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4600. -/
theorem noS8R164_Law4600 : ∀ v : Magma.tup8R164,
    ¬ @Equation4600 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4600) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4600) (by native_decide) v.1 v.2
    ((@Law4600.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4601 takes them (13 nodes). -/
def ordS8R164_Law4601 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4601. -/
theorem noS8R164_Law4601 : ∀ v : Magma.tup8R164,
    ¬ @Equation4601 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4601) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4601) (by native_decide) v.1 v.2
    ((@Law4601.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4602 takes them (13 nodes). -/
def ordS8R164_Law4602 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4602. -/
theorem noS8R164_Law4602 : ∀ v : Magma.tup8R164,
    ¬ @Equation4602 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4602) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4602) (by native_decide) v.1 v.2
    ((@Law4602.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4603 takes them (10 nodes). -/
def ordS8R164_Law4603 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4603. -/
theorem noS8R164_Law4603 : ∀ v : Magma.tup8R164,
    ¬ @Equation4603 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4603) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4603) (by native_decide) v.1 v.2
    ((@Law4603.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4604 takes them (9 nodes). -/
def ordS8R164_Law4604 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4604. -/
theorem noS8R164_Law4604 : ∀ v : Magma.tup8R164,
    ¬ @Equation4604 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4604) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4604) (by native_decide) v.1 v.2
    ((@Law4604.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4606 takes them (24 nodes). -/
def ordS8R164_Law4606 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4606. -/
theorem noS8R164_Law4606 : ∀ v : Magma.tup8R164,
    ¬ @Equation4606 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4606) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4606) (by native_decide) v.1 v.2
    ((@Law4606.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4607 takes them (6 nodes). -/
def ordS8R164_Law4607 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4607. -/
theorem noS8R164_Law4607 : ∀ v : Magma.tup8R164,
    ¬ @Equation4607 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4607) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4607) (by native_decide) v.1 v.2
    ((@Law4607.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4610 takes them (7 nodes). -/
def ordS8R164_Law4610 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4610. -/
theorem noS8R164_Law4610 : ∀ v : Magma.tup8R164,
    ¬ @Equation4610 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4610) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4610) (by native_decide) v.1 v.2
    ((@Law4610.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4611 takes them (18 nodes). -/
def ordS8R164_Law4611 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4611. -/
theorem noS8R164_Law4611 : ∀ v : Magma.tup8R164,
    ¬ @Equation4611 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4611) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4611) (by native_decide) v.1 v.2
    ((@Law4611.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4613 takes them (6 nodes). -/
def ordS8R164_Law4613 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4613. -/
theorem noS8R164_Law4613 : ∀ v : Magma.tup8R164,
    ¬ @Equation4613 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4613) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4613) (by native_decide) v.1 v.2
    ((@Law4613.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4614 takes them (7 nodes). -/
def ordS8R164_Law4614 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4614. -/
theorem noS8R164_Law4614 : ∀ v : Magma.tup8R164,
    ¬ @Equation4614 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4614) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4614) (by native_decide) v.1 v.2
    ((@Law4614.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4615 takes them (10 nodes). -/
def ordS8R164_Law4615 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4615. -/
theorem noS8R164_Law4615 : ∀ v : Magma.tup8R164,
    ¬ @Equation4615 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4615) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4615) (by native_decide) v.1 v.2
    ((@Law4615.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4616 takes them (11 nodes). -/
def ordS8R164_Law4616 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4616. -/
theorem noS8R164_Law4616 : ∀ v : Magma.tup8R164,
    ¬ @Equation4616 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4616) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4616) (by native_decide) v.1 v.2
    ((@Law4616.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4617 takes them (6 nodes). -/
def ordS8R164_Law4617 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4617. -/
theorem noS8R164_Law4617 : ∀ v : Magma.tup8R164,
    ¬ @Equation4617 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4617) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4617) (by native_decide) v.1 v.2
    ((@Law4617.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4618 takes them (7 nodes). -/
def ordS8R164_Law4618 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4618. -/
theorem noS8R164_Law4618 : ∀ v : Magma.tup8R164,
    ¬ @Equation4618 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4618) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4618) (by native_decide) v.1 v.2
    ((@Law4618.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4619 takes them (11 nodes). -/
def ordS8R164_Law4619 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4619. -/
theorem noS8R164_Law4619 : ∀ v : Magma.tup8R164,
    ¬ @Equation4619 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4619) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4619) (by native_decide) v.1 v.2
    ((@Law4619.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4621 takes them (6 nodes). -/
def ordS8R164_Law4621 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4621. -/
theorem noS8R164_Law4621 : ∀ v : Magma.tup8R164,
    ¬ @Equation4621 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4621) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4621) (by native_decide) v.1 v.2
    ((@Law4621.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4624 takes them (6 nodes). -/
def ordS8R164_Law4624 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4624. -/
theorem noS8R164_Law4624 : ∀ v : Magma.tup8R164,
    ¬ @Equation4624 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4624) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4624) (by native_decide) v.1 v.2
    ((@Law4624.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4625 takes them (10 nodes). -/
def ordS8R164_Law4625 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4625. -/
theorem noS8R164_Law4625 : ∀ v : Magma.tup8R164,
    ¬ @Equation4625 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4625) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4625) (by native_decide) v.1 v.2
    ((@Law4625.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4626 takes them (11 nodes). -/
def ordS8R164_Law4626 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4626. -/
theorem noS8R164_Law4626 : ∀ v : Magma.tup8R164,
    ¬ @Equation4626 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4626) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4626) (by native_decide) v.1 v.2
    ((@Law4626.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4627 takes them (7 nodes). -/
def ordS8R164_Law4627 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4627. -/
theorem noS8R164_Law4627 : ∀ v : Magma.tup8R164,
    ¬ @Equation4627 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4627) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4627) (by native_decide) v.1 v.2
    ((@Law4627.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4628 takes them (6 nodes). -/
def ordS8R164_Law4628 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4628. -/
theorem noS8R164_Law4628 : ∀ v : Magma.tup8R164,
    ¬ @Equation4628 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4628) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4628) (by native_decide) v.1 v.2
    ((@Law4628.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (17 nodes). -/
def ordS8R164_Law4629 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4629. -/
theorem noS8R164_Law4629 : ∀ v : Magma.tup8R164,
    ¬ @Equation4629 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4630 takes them (9 nodes). -/
def ordS8R164_Law4630 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4630. -/
theorem noS8R164_Law4630 : ∀ v : Magma.tup8R164,
    ¬ @Equation4630 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4630) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4630) (by native_decide) v.1 v.2
    ((@Law4630.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4631 takes them (23 nodes). -/
def ordS8R164_Law4631 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4631. -/
theorem noS8R164_Law4631 : ∀ v : Magma.tup8R164,
    ¬ @Equation4631 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4631) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4631) (by native_decide) v.1 v.2
    ((@Law4631.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4632 takes them (10 nodes). -/
def ordS8R164_Law4632 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4632. -/
theorem noS8R164_Law4632 : ∀ v : Magma.tup8R164,
    ¬ @Equation4632 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4632) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4632) (by native_decide) v.1 v.2
    ((@Law4632.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4633 takes them (10 nodes). -/
def ordS8R164_Law4633 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4633. -/
theorem noS8R164_Law4633 : ∀ v : Magma.tup8R164,
    ¬ @Equation4633 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4633) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4633) (by native_decide) v.1 v.2
    ((@Law4633.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4634 takes them (9 nodes). -/
def ordS8R164_Law4634 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4634. -/
theorem noS8R164_Law4634 : ∀ v : Magma.tup8R164,
    ¬ @Equation4634 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4634) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4634) (by native_decide) v.1 v.2
    ((@Law4634.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4636 takes them (16 nodes). -/
def ordS8R164_Law4636 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4636. -/
theorem noS8R164_Law4636 : ∀ v : Magma.tup8R164,
    ¬ @Equation4636 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4636) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4636) (by native_decide) v.1 v.2
    ((@Law4636.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4637 takes them (6 nodes). -/
def ordS8R164_Law4637 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4637. -/
theorem noS8R164_Law4637 : ∀ v : Magma.tup8R164,
    ¬ @Equation4637 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4637) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4637) (by native_decide) v.1 v.2
    ((@Law4637.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4638 takes them (10 nodes). -/
def ordS8R164_Law4638 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4638. -/
theorem noS8R164_Law4638 : ∀ v : Magma.tup8R164,
    ¬ @Equation4638 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4638) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4638) (by native_decide) v.1 v.2
    ((@Law4638.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4639 takes them (12 nodes). -/
def ordS8R164_Law4639 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4639. -/
theorem noS8R164_Law4639 : ∀ v : Magma.tup8R164,
    ¬ @Equation4639 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4639) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4639) (by native_decide) v.1 v.2
    ((@Law4639.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4641 takes them (6 nodes). -/
def ordS8R164_Law4641 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4641. -/
theorem noS8R164_Law4641 : ∀ v : Magma.tup8R164,
    ¬ @Equation4641 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4641) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4641) (by native_decide) v.1 v.2
    ((@Law4641.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4642 takes them (11 nodes). -/
def ordS8R164_Law4642 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4642. -/
theorem noS8R164_Law4642 : ∀ v : Magma.tup8R164,
    ¬ @Equation4642 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4642) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4642) (by native_decide) v.1 v.2
    ((@Law4642.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4643 takes them (7 nodes). -/
def ordS8R164_Law4643 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4643. -/
theorem noS8R164_Law4643 : ∀ v : Magma.tup8R164,
    ¬ @Equation4643 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4643) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4643) (by native_decide) v.1 v.2
    ((@Law4643.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4644 takes them (6 nodes). -/
def ordS8R164_Law4644 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4644. -/
theorem noS8R164_Law4644 : ∀ v : Magma.tup8R164,
    ¬ @Equation4644 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4644) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4644) (by native_decide) v.1 v.2
    ((@Law4644.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4645 takes them (10 nodes). -/
def ordS8R164_Law4645 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4645. -/
theorem noS8R164_Law4645 : ∀ v : Magma.tup8R164,
    ¬ @Equation4645 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4645) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4645) (by native_decide) v.1 v.2
    ((@Law4645.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4646 takes them (7 nodes). -/
def ordS8R164_Law4646 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4646. -/
theorem noS8R164_Law4646 : ∀ v : Magma.tup8R164,
    ¬ @Equation4646 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4646) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4646) (by native_decide) v.1 v.2
    ((@Law4646.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4648 takes them (6 nodes). -/
def ordS8R164_Law4648 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4648. -/
theorem noS8R164_Law4648 : ∀ v : Magma.tup8R164,
    ¬ @Equation4648 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4648) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4648) (by native_decide) v.1 v.2
    ((@Law4648.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4649 takes them (10 nodes). -/
def ordS8R164_Law4649 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4649. -/
theorem noS8R164_Law4649 : ∀ v : Magma.tup8R164,
    ¬ @Equation4649 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4649) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4649) (by native_decide) v.1 v.2
    ((@Law4649.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4650 takes them (7 nodes). -/
def ordS8R164_Law4650 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4650. -/
theorem noS8R164_Law4650 : ∀ v : Magma.tup8R164,
    ¬ @Equation4650 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4650) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4650) (by native_decide) v.1 v.2
    ((@Law4650.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4651 takes them (12 nodes). -/
def ordS8R164_Law4651 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4651. -/
theorem noS8R164_Law4651 : ∀ v : Magma.tup8R164,
    ¬ @Equation4651 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4651) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4651) (by native_decide) v.1 v.2
    ((@Law4651.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4652 takes them (7 nodes). -/
def ordS8R164_Law4652 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4652. -/
theorem noS8R164_Law4652 : ∀ v : Magma.tup8R164,
    ¬ @Equation4652 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4652) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4652) (by native_decide) v.1 v.2
    ((@Law4652.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4653 takes them (6 nodes). -/
def ordS8R164_Law4653 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4653. -/
theorem noS8R164_Law4653 : ∀ v : Magma.tup8R164,
    ¬ @Equation4653 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4653) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4653) (by native_decide) v.1 v.2
    ((@Law4653.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4654 takes them (9 nodes). -/
def ordS8R164_Law4654 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4654. -/
theorem noS8R164_Law4654 : ∀ v : Magma.tup8R164,
    ¬ @Equation4654 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4654) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4654) (by native_decide) v.1 v.2
    ((@Law4654.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4655 takes them (13 nodes). -/
def ordS8R164_Law4655 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4655. -/
theorem noS8R164_Law4655 : ∀ v : Magma.tup8R164,
    ¬ @Equation4655 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4655) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4655) (by native_decide) v.1 v.2
    ((@Law4655.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4657 takes them (9 nodes). -/
def ordS8R164_Law4657 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4657. -/
theorem noS8R164_Law4657 : ∀ v : Magma.tup8R164,
    ¬ @Equation4657 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4657) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4657) (by native_decide) v.1 v.2
    ((@Law4657.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4658 takes them (15 nodes). -/
def ordS8R164_Law4658 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4658. -/
theorem noS8R164_Law4658 : ∀ v : Magma.tup8R164,
    ¬ @Equation4658 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4658) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law4658) (by native_decide) v.1 v.2
    ((@Law4658.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4659 takes them (6 nodes). -/
def ordS8R164_Law4659 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4659. -/
theorem noS8R164_Law4659 : ∀ v : Magma.tup8R164,
    ¬ @Equation4659 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4659) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4659) (by native_decide) v.1 v.2
    ((@Law4659.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4660 takes them (7 nodes). -/
def ordS8R164_Law4660 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4660. -/
theorem noS8R164_Law4660 : ∀ v : Magma.tup8R164,
    ¬ @Equation4660 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4660) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4660) (by native_decide) v.1 v.2
    ((@Law4660.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4661 takes them (9 nodes). -/
def ordS8R164_Law4661 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4661. -/
theorem noS8R164_Law4661 : ∀ v : Magma.tup8R164,
    ¬ @Equation4661 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4661) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4661) (by native_decide) v.1 v.2
    ((@Law4661.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4662 takes them (6 nodes). -/
def ordS8R164_Law4662 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4662. -/
theorem noS8R164_Law4662 : ∀ v : Magma.tup8R164,
    ¬ @Equation4662 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4662) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4662) (by native_decide) v.1 v.2
    ((@Law4662.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4663 takes them (10 nodes). -/
def ordS8R164_Law4663 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4663. -/
theorem noS8R164_Law4663 : ∀ v : Magma.tup8R164,
    ¬ @Equation4663 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4663) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4663) (by native_decide) v.1 v.2
    ((@Law4663.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4664 takes them (6 nodes). -/
def ordS8R164_Law4664 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4664. -/
theorem noS8R164_Law4664 : ∀ v : Magma.tup8R164,
    ¬ @Equation4664 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4664) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4664) (by native_decide) v.1 v.2
    ((@Law4664.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4665 takes them (7 nodes). -/
def ordS8R164_Law4665 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4665. -/
theorem noS8R164_Law4665 : ∀ v : Magma.tup8R164,
    ¬ @Equation4665 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4665) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4665) (by native_decide) v.1 v.2
    ((@Law4665.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4666 takes them (12 nodes). -/
def ordS8R164_Law4666 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4666. -/
theorem noS8R164_Law4666 : ∀ v : Magma.tup8R164,
    ¬ @Equation4666 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4666) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4666) (by native_decide) v.1 v.2
    ((@Law4666.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4667 takes them (6 nodes). -/
def ordS8R164_Law4667 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4667. -/
theorem noS8R164_Law4667 : ∀ v : Magma.tup8R164,
    ¬ @Equation4667 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4667) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4667) (by native_decide) v.1 v.2
    ((@Law4667.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4668 takes them (7 nodes). -/
def ordS8R164_Law4668 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4668. -/
theorem noS8R164_Law4668 : ∀ v : Magma.tup8R164,
    ¬ @Equation4668 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4668) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4668) (by native_decide) v.1 v.2
    ((@Law4668.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4669 takes them (10 nodes). -/
def ordS8R164_Law4669 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4669. -/
theorem noS8R164_Law4669 : ∀ v : Magma.tup8R164,
    ¬ @Equation4669 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4669) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4669) (by native_decide) v.1 v.2
    ((@Law4669.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4670 takes them (9 nodes). -/
def ordS8R164_Law4670 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4670. -/
theorem noS8R164_Law4670 : ∀ v : Magma.tup8R164,
    ¬ @Equation4670 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4670) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4670) (by native_decide) v.1 v.2
    ((@Law4670.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `80` equations. -/
theorem srch8R164_refutes_16 :
    FamilyRefutes Magma.srch8R164 [
      4572, 4573, 4574, 4575, 4576, 4577, 4578, 4579, 4580, 4581, 4582, 4584, 4586, 4587, 4589,
      4593, 4594, 4595, 4596, 4599, 4600, 4601, 4602, 4603, 4604, 4606, 4607, 4610, 4611, 4613,
      4614, 4615, 4616, 4617, 4618, 4619, 4621, 4624, 4625, 4626, 4627, 4628, 4629, 4630, 4631,
      4632, 4633, 4634, 4636, 4637, 4638, 4639, 4641, 4642, 4643, 4644, 4645, 4646, 4648, 4649,
      4650, 4651, 4652, 4653, 4654, 4655, 4657, 4658, 4659, 4660, 4661, 4662, 4663, 4664, 4665,
      4666, 4667, 4668, 4669, 4670
    ] :=
  ⟨noS8R164_Law4572, noS8R164_Law4573, noS8R164_Law4574, noS8R164_Law4575, noS8R164_Law4576, noS8R164_Law4577, noS8R164_Law4578, noS8R164_Law4579, noS8R164_Law4580, noS8R164_Law4581, noS8R164_Law4582, noS8R164_Law4584, noS8R164_Law4586, noS8R164_Law4587, noS8R164_Law4589, noS8R164_Law4593, noS8R164_Law4594, noS8R164_Law4595, noS8R164_Law4596, noS8R164_Law4599, noS8R164_Law4600, noS8R164_Law4601, noS8R164_Law4602, noS8R164_Law4603, noS8R164_Law4604, noS8R164_Law4606, noS8R164_Law4607, noS8R164_Law4610, noS8R164_Law4611, noS8R164_Law4613, noS8R164_Law4614, noS8R164_Law4615, noS8R164_Law4616, noS8R164_Law4617, noS8R164_Law4618, noS8R164_Law4619, noS8R164_Law4621, noS8R164_Law4624, noS8R164_Law4625, noS8R164_Law4626, noS8R164_Law4627, noS8R164_Law4628, noS8R164_Law4629, noS8R164_Law4630, noS8R164_Law4631, noS8R164_Law4632, noS8R164_Law4633, noS8R164_Law4634, noS8R164_Law4636, noS8R164_Law4637, noS8R164_Law4638, noS8R164_Law4639, noS8R164_Law4641, noS8R164_Law4642, noS8R164_Law4643, noS8R164_Law4644, noS8R164_Law4645, noS8R164_Law4646, noS8R164_Law4648, noS8R164_Law4649, noS8R164_Law4650, noS8R164_Law4651, noS8R164_Law4652, noS8R164_Law4653, noS8R164_Law4654, noS8R164_Law4655, noS8R164_Law4657, noS8R164_Law4658, noS8R164_Law4659, noS8R164_Law4660, noS8R164_Law4661, noS8R164_Law4662, noS8R164_Law4663, noS8R164_Law4664, noS8R164_Law4665, noS8R164_Law4666, noS8R164_Law4667, noS8R164_Law4668, noS8R164_Law4669, noS8R164_Law4670⟩
