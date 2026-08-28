import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 45 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `32`
equations here, 2,600 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3971 takes them (112 nodes). -/
def ordS6A_Law3971 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3971. -/
theorem noS6A_Law3971 : ∀ v : Magma.tupS6A,
    ¬ @Equation3971 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3971) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3971) (by native_decide) v.1 v.2
    ((@Law3971.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3973 takes them (162 nodes). -/
def ordS6A_Law3973 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3973. -/
theorem noS6A_Law3973 : ∀ v : Magma.tupS6A,
    ¬ @Equation3973 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3973) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3973) (by native_decide) v.1 v.2
    ((@Law3973.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3974 takes them (47 nodes). -/
def ordS6A_Law3974 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3974. -/
theorem noS6A_Law3974 : ∀ v : Magma.tupS6A,
    ¬ @Equation3974 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3974) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3974) (by native_decide) v.1 v.2
    ((@Law3974.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3975 takes them (88 nodes). -/
def ordS6A_Law3975 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3975. -/
theorem noS6A_Law3975 : ∀ v : Magma.tupS6A,
    ¬ @Equation3975 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3975) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3975) (by native_decide) v.1 v.2
    ((@Law3975.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3976 takes them (162 nodes). -/
def ordS6A_Law3976 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3976. -/
theorem noS6A_Law3976 : ∀ v : Magma.tupS6A,
    ¬ @Equation3976 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3976) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3976) (by native_decide) v.1 v.2
    ((@Law3976.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3977 takes them (72 nodes). -/
def ordS6A_Law3977 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3977. -/
theorem noS6A_Law3977 : ∀ v : Magma.tupS6A,
    ¬ @Equation3977 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3977) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3977) (by native_decide) v.1 v.2
    ((@Law3977.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3978 takes them (51 nodes). -/
def ordS6A_Law3978 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3978. -/
theorem noS6A_Law3978 : ∀ v : Magma.tupS6A,
    ¬ @Equation3978 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3978) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3978) (by native_decide) v.1 v.2
    ((@Law3978.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3980 takes them (175 nodes). -/
def ordS6A_Law3980 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3980. -/
theorem noS6A_Law3980 : ∀ v : Magma.tupS6A,
    ¬ @Equation3980 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3980) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3980) (by native_decide) v.1 v.2
    ((@Law3980.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3981 takes them (113 nodes). -/
def ordS6A_Law3981 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3981. -/
theorem noS6A_Law3981 : ∀ v : Magma.tupS6A,
    ¬ @Equation3981 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3981) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3981) (by native_decide) v.1 v.2
    ((@Law3981.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3982 takes them (74 nodes). -/
def ordS6A_Law3982 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3982. -/
theorem noS6A_Law3982 : ∀ v : Magma.tupS6A,
    ¬ @Equation3982 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3982) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3982) (by native_decide) v.1 v.2
    ((@Law3982.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3983 takes them (79 nodes). -/
def ordS6A_Law3983 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3983. -/
theorem noS6A_Law3983 : ∀ v : Magma.tupS6A,
    ¬ @Equation3983 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3983) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3983) (by native_decide) v.1 v.2
    ((@Law3983.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3984 takes them (139 nodes). -/
def ordS6A_Law3984 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3984. -/
theorem noS6A_Law3984 : ∀ v : Magma.tupS6A,
    ¬ @Equation3984 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3984) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3984) (by native_decide) v.1 v.2
    ((@Law3984.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3985 takes them (65 nodes). -/
def ordS6A_Law3985 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3985. -/
theorem noS6A_Law3985 : ∀ v : Magma.tupS6A,
    ¬ @Equation3985 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3985) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3985) (by native_decide) v.1 v.2
    ((@Law3985.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3986 takes them (67 nodes). -/
def ordS6A_Law3986 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3986. -/
theorem noS6A_Law3986 : ∀ v : Magma.tupS6A,
    ¬ @Equation3986 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3986) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3986) (by native_decide) v.1 v.2
    ((@Law3986.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3987 takes them (44 nodes). -/
def ordS6A_Law3987 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3987. -/
theorem noS6A_Law3987 : ∀ v : Magma.tupS6A,
    ¬ @Equation3987 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3987) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3987) (by native_decide) v.1 v.2
    ((@Law3987.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3988 takes them (64 nodes). -/
def ordS6A_Law3988 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3988. -/
theorem noS6A_Law3988 : ∀ v : Magma.tupS6A,
    ¬ @Equation3988 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3988) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3988) (by native_decide) v.1 v.2
    ((@Law3988.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3990 takes them (76 nodes). -/
def ordS6A_Law3990 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3990. -/
theorem noS6A_Law3990 : ∀ v : Magma.tupS6A,
    ¬ @Equation3990 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3990) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3990) (by native_decide) v.1 v.2
    ((@Law3990.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3991 takes them (64 nodes). -/
def ordS6A_Law3991 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3991. -/
theorem noS6A_Law3991 : ∀ v : Magma.tupS6A,
    ¬ @Equation3991 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3991) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3991) (by native_decide) v.1 v.2
    ((@Law3991.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3992 takes them (89 nodes). -/
def ordS6A_Law3992 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3992. -/
theorem noS6A_Law3992 : ∀ v : Magma.tupS6A,
    ¬ @Equation3992 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3992) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3992) (by native_decide) v.1 v.2
    ((@Law3992.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3995 takes them (39 nodes). -/
def ordS6A_Law3995 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3995. -/
theorem noS6A_Law3995 : ∀ v : Magma.tupS6A,
    ¬ @Equation3995 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3995) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3995) (by native_decide) v.1 v.2
    ((@Law3995.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3996 takes them (34 nodes). -/
def ordS6A_Law3996 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3996. -/
theorem noS6A_Law3996 : ∀ v : Magma.tupS6A,
    ¬ @Equation3996 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3996) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3996) (by native_decide) v.1 v.2
    ((@Law3996.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3998 takes them (34 nodes). -/
def ordS6A_Law3998 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3998. -/
theorem noS6A_Law3998 : ∀ v : Magma.tupS6A,
    ¬ @Equation3998 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3998) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3998) (by native_decide) v.1 v.2
    ((@Law3998.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3999 takes them (34 nodes). -/
def ordS6A_Law3999 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3999. -/
theorem noS6A_Law3999 : ∀ v : Magma.tupS6A,
    ¬ @Equation3999 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3999) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3999) (by native_decide) v.1 v.2
    ((@Law3999.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4000 takes them (27 nodes). -/
def ordS6A_Law4000 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4000. -/
theorem noS6A_Law4000 : ∀ v : Magma.tupS6A,
    ¬ @Equation4000 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4000) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4000) (by native_decide) v.1 v.2
    ((@Law4000.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4001 takes them (92 nodes). -/
def ordS6A_Law4001 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4001. -/
theorem noS6A_Law4001 : ∀ v : Magma.tupS6A,
    ¬ @Equation4001 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4001) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4001) (by native_decide) v.1 v.2
    ((@Law4001.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4002 takes them (27 nodes). -/
def ordS6A_Law4002 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4002. -/
theorem noS6A_Law4002 : ∀ v : Magma.tupS6A,
    ¬ @Equation4002 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4002) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4002) (by native_decide) v.1 v.2
    ((@Law4002.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4003 takes them (27 nodes). -/
def ordS6A_Law4003 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4003. -/
theorem noS6A_Law4003 : ∀ v : Magma.tupS6A,
    ¬ @Equation4003 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4003) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4003) (by native_decide) v.1 v.2
    ((@Law4003.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4004 takes them (27 nodes). -/
def ordS6A_Law4004 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4004. -/
theorem noS6A_Law4004 : ∀ v : Magma.tupS6A,
    ¬ @Equation4004 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4004) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4004) (by native_decide) v.1 v.2
    ((@Law4004.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4005 takes them (114 nodes). -/
def ordS6A_Law4005 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4005. -/
theorem noS6A_Law4005 : ∀ v : Magma.tupS6A,
    ¬ @Equation4005 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4005) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4005) (by native_decide) v.1 v.2
    ((@Law4005.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4008 takes them (50 nodes). -/
def ordS6A_Law4008 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4008. -/
theorem noS6A_Law4008 : ∀ v : Magma.tupS6A,
    ¬ @Equation4008 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4008) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law4008) (by native_decide) v.1 v.2
    ((@Law4008.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4009 takes them (126 nodes). -/
def ordS6A_Law4009 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4009. -/
theorem noS6A_Law4009 : ∀ v : Magma.tupS6A,
    ¬ @Equation4009 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4009) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4009) (by native_decide) v.1 v.2
    ((@Law4009.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4010 takes them (226 nodes). -/
def ordS6A_Law4010 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4010. -/
theorem noS6A_Law4010 : ∀ v : Magma.tupS6A,
    ¬ @Equation4010 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4010) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law4010) (by native_decide) v.1 v.2
    ((@Law4010.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `32` equations. -/
theorem srch6A_refutes_44 :
    FamilyRefutes Magma.srch6A [
      3971, 3973, 3974, 3975, 3976, 3977, 3978, 3980, 3981, 3982, 3983, 3984, 3985, 3986, 3987,
      3988, 3990, 3991, 3992, 3995, 3996, 3998, 3999, 4000, 4001, 4002, 4003, 4004, 4005, 4008,
      4009, 4010
    ] :=
  ⟨noS6A_Law3971, noS6A_Law3973, noS6A_Law3974, noS6A_Law3975, noS6A_Law3976, noS6A_Law3977, noS6A_Law3978, noS6A_Law3980, noS6A_Law3981, noS6A_Law3982, noS6A_Law3983, noS6A_Law3984, noS6A_Law3985, noS6A_Law3986, noS6A_Law3987, noS6A_Law3988, noS6A_Law3990, noS6A_Law3991, noS6A_Law3992, noS6A_Law3995, noS6A_Law3996, noS6A_Law3998, noS6A_Law3999, noS6A_Law4000, noS6A_Law4001, noS6A_Law4002, noS6A_Law4003, noS6A_Law4004, noS6A_Law4005, noS6A_Law4008, noS6A_Law4009, noS6A_Law4010⟩
