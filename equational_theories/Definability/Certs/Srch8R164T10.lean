import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 11 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `84` equations here, 601 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3969 takes them (7 nodes). -/
def ordS8R164_Law3969 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3969. -/
theorem noS8R164_Law3969 : ∀ v : Magma.tup8R164,
    ¬ @Equation3969 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3969) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3969) (by native_decide) v.1 v.2
    ((@Law3969.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3970 takes them (6 nodes). -/
def ordS8R164_Law3970 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3970. -/
theorem noS8R164_Law3970 : ∀ v : Magma.tup8R164,
    ¬ @Equation3970 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3970) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3970) (by native_decide) v.1 v.2
    ((@Law3970.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3971 takes them (7 nodes). -/
def ordS8R164_Law3971 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3971. -/
theorem noS8R164_Law3971 : ∀ v : Magma.tup8R164,
    ¬ @Equation3971 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3971) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3971) (by native_decide) v.1 v.2
    ((@Law3971.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (10 nodes). -/
def ordS8R164_Law3972 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3972. -/
theorem noS8R164_Law3972 : ∀ v : Magma.tup8R164,
    ¬ @Equation3972 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3974 takes them (6 nodes). -/
def ordS8R164_Law3974 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3974. -/
theorem noS8R164_Law3974 : ∀ v : Magma.tup8R164,
    ¬ @Equation3974 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3974) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3974) (by native_decide) v.1 v.2
    ((@Law3974.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3975 takes them (7 nodes). -/
def ordS8R164_Law3975 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3975. -/
theorem noS8R164_Law3975 : ∀ v : Magma.tup8R164,
    ¬ @Equation3975 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3975) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3975) (by native_decide) v.1 v.2
    ((@Law3975.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3976 takes them (10 nodes). -/
def ordS8R164_Law3976 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3976. -/
theorem noS8R164_Law3976 : ∀ v : Magma.tup8R164,
    ¬ @Equation3976 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3976) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3976) (by native_decide) v.1 v.2
    ((@Law3976.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3977 takes them (7 nodes). -/
def ordS8R164_Law3977 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3977. -/
theorem noS8R164_Law3977 : ∀ v : Magma.tup8R164,
    ¬ @Equation3977 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3977) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3977) (by native_decide) v.1 v.2
    ((@Law3977.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3978 takes them (6 nodes). -/
def ordS8R164_Law3978 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3978. -/
theorem noS8R164_Law3978 : ∀ v : Magma.tup8R164,
    ¬ @Equation3978 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3978) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3978) (by native_decide) v.1 v.2
    ((@Law3978.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3980 takes them (10 nodes). -/
def ordS8R164_Law3980 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3980. -/
theorem noS8R164_Law3980 : ∀ v : Magma.tup8R164,
    ¬ @Equation3980 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3980) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3980) (by native_decide) v.1 v.2
    ((@Law3980.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3981 takes them (7 nodes). -/
def ordS8R164_Law3981 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3981. -/
theorem noS8R164_Law3981 : ∀ v : Magma.tup8R164,
    ¬ @Equation3981 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3981) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3981) (by native_decide) v.1 v.2
    ((@Law3981.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3982 takes them (6 nodes). -/
def ordS8R164_Law3982 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3982. -/
theorem noS8R164_Law3982 : ∀ v : Magma.tup8R164,
    ¬ @Equation3982 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3982) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3982) (by native_decide) v.1 v.2
    ((@Law3982.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3983 takes them (7 nodes). -/
def ordS8R164_Law3983 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3983. -/
theorem noS8R164_Law3983 : ∀ v : Magma.tup8R164,
    ¬ @Equation3983 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3983) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3983) (by native_decide) v.1 v.2
    ((@Law3983.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3984 takes them (10 nodes). -/
def ordS8R164_Law3984 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3984. -/
theorem noS8R164_Law3984 : ∀ v : Magma.tup8R164,
    ¬ @Equation3984 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3984) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3984) (by native_decide) v.1 v.2
    ((@Law3984.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3985 takes them (7 nodes). -/
def ordS8R164_Law3985 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3985. -/
theorem noS8R164_Law3985 : ∀ v : Magma.tup8R164,
    ¬ @Equation3985 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3985) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3985) (by native_decide) v.1 v.2
    ((@Law3985.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3986 takes them (7 nodes). -/
def ordS8R164_Law3986 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3986. -/
theorem noS8R164_Law3986 : ∀ v : Magma.tup8R164,
    ¬ @Equation3986 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3986) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3986) (by native_decide) v.1 v.2
    ((@Law3986.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3987 takes them (6 nodes). -/
def ordS8R164_Law3987 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3987. -/
theorem noS8R164_Law3987 : ∀ v : Magma.tup8R164,
    ¬ @Equation3987 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3987) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3987) (by native_decide) v.1 v.2
    ((@Law3987.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3988 takes them (6 nodes). -/
def ordS8R164_Law3988 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3988. -/
theorem noS8R164_Law3988 : ∀ v : Magma.tup8R164,
    ¬ @Equation3988 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3988) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3988) (by native_decide) v.1 v.2
    ((@Law3988.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (10 nodes). -/
def ordS8R164_Law3989 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3989. -/
theorem noS8R164_Law3989 : ∀ v : Magma.tup8R164,
    ¬ @Equation3989 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3990 takes them (7 nodes). -/
def ordS8R164_Law3990 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3990. -/
theorem noS8R164_Law3990 : ∀ v : Magma.tup8R164,
    ¬ @Equation3990 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3990) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3990) (by native_decide) v.1 v.2
    ((@Law3990.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3991 takes them (6 nodes). -/
def ordS8R164_Law3991 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3991. -/
theorem noS8R164_Law3991 : ∀ v : Magma.tup8R164,
    ¬ @Equation3991 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3991) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3991) (by native_decide) v.1 v.2
    ((@Law3991.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3992 takes them (7 nodes). -/
def ordS8R164_Law3992 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3992. -/
theorem noS8R164_Law3992 : ∀ v : Magma.tup8R164,
    ¬ @Equation3992 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3992) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3992) (by native_decide) v.1 v.2
    ((@Law3992.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3993 takes them (10 nodes). -/
def ordS8R164_Law3993 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3993. -/
theorem noS8R164_Law3993 : ∀ v : Magma.tup8R164,
    ¬ @Equation3993 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3993) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3993) (by native_decide) v.1 v.2
    ((@Law3993.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3995 takes them (6 nodes). -/
def ordS8R164_Law3995 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3995. -/
theorem noS8R164_Law3995 : ∀ v : Magma.tup8R164,
    ¬ @Equation3995 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3995) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3995) (by native_decide) v.1 v.2
    ((@Law3995.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3996 takes them (6 nodes). -/
def ordS8R164_Law3996 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3996. -/
theorem noS8R164_Law3996 : ∀ v : Magma.tup8R164,
    ¬ @Equation3996 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3996) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3996) (by native_decide) v.1 v.2
    ((@Law3996.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3998 takes them (6 nodes). -/
def ordS8R164_Law3998 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3998. -/
theorem noS8R164_Law3998 : ∀ v : Magma.tup8R164,
    ¬ @Equation3998 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3998) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3998) (by native_decide) v.1 v.2
    ((@Law3998.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3999 takes them (6 nodes). -/
def ordS8R164_Law3999 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3999. -/
theorem noS8R164_Law3999 : ∀ v : Magma.tup8R164,
    ¬ @Equation3999 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3999) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3999) (by native_decide) v.1 v.2
    ((@Law3999.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4000 takes them (6 nodes). -/
def ordS8R164_Law4000 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4000. -/
theorem noS8R164_Law4000 : ∀ v : Magma.tup8R164,
    ¬ @Equation4000 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4000) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4000) (by native_decide) v.1 v.2
    ((@Law4000.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4001 takes them (10 nodes). -/
def ordS8R164_Law4001 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4001. -/
theorem noS8R164_Law4001 : ∀ v : Magma.tup8R164,
    ¬ @Equation4001 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4001) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4001) (by native_decide) v.1 v.2
    ((@Law4001.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4002 takes them (6 nodes). -/
def ordS8R164_Law4002 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4002. -/
theorem noS8R164_Law4002 : ∀ v : Magma.tup8R164,
    ¬ @Equation4002 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4002) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4002) (by native_decide) v.1 v.2
    ((@Law4002.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4003 takes them (6 nodes). -/
def ordS8R164_Law4003 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4003. -/
theorem noS8R164_Law4003 : ∀ v : Magma.tup8R164,
    ¬ @Equation4003 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4003) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4003) (by native_decide) v.1 v.2
    ((@Law4003.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4004 takes them (6 nodes). -/
def ordS8R164_Law4004 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4004. -/
theorem noS8R164_Law4004 : ∀ v : Magma.tup8R164,
    ¬ @Equation4004 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4004) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4004) (by native_decide) v.1 v.2
    ((@Law4004.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4005 takes them (7 nodes). -/
def ordS8R164_Law4005 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4005. -/
theorem noS8R164_Law4005 : ∀ v : Magma.tup8R164,
    ¬ @Equation4005 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4005) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4005) (by native_decide) v.1 v.2
    ((@Law4005.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4006 takes them (10 nodes). -/
def ordS8R164_Law4006 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4006. -/
theorem noS8R164_Law4006 : ∀ v : Magma.tup8R164,
    ¬ @Equation4006 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4008 takes them (6 nodes). -/
def ordS8R164_Law4008 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4008. -/
theorem noS8R164_Law4008 : ∀ v : Magma.tup8R164,
    ¬ @Equation4008 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4008) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4008) (by native_decide) v.1 v.2
    ((@Law4008.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4009 takes them (7 nodes). -/
def ordS8R164_Law4009 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4009. -/
theorem noS8R164_Law4009 : ∀ v : Magma.tup8R164,
    ¬ @Equation4009 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4009) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4009) (by native_decide) v.1 v.2
    ((@Law4009.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4010 takes them (10 nodes). -/
def ordS8R164_Law4010 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4010. -/
theorem noS8R164_Law4010 : ∀ v : Magma.tup8R164,
    ¬ @Equation4010 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4010) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4010) (by native_decide) v.1 v.2
    ((@Law4010.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4011 takes them (7 nodes). -/
def ordS8R164_Law4011 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4011. -/
theorem noS8R164_Law4011 : ∀ v : Magma.tup8R164,
    ¬ @Equation4011 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4011) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4011) (by native_decide) v.1 v.2
    ((@Law4011.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4012 takes them (6 nodes). -/
def ordS8R164_Law4012 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4012. -/
theorem noS8R164_Law4012 : ∀ v : Magma.tup8R164,
    ¬ @Equation4012 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4012) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4012) (by native_decide) v.1 v.2
    ((@Law4012.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4014 takes them (10 nodes). -/
def ordS8R164_Law4014 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4014. -/
theorem noS8R164_Law4014 : ∀ v : Magma.tup8R164,
    ¬ @Equation4014 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4014) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4014) (by native_decide) v.1 v.2
    ((@Law4014.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4015 takes them (7 nodes). -/
def ordS8R164_Law4015 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4015. -/
theorem noS8R164_Law4015 : ∀ v : Magma.tup8R164,
    ¬ @Equation4015 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4015) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4015) (by native_decide) v.1 v.2
    ((@Law4015.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4016 takes them (6 nodes). -/
def ordS8R164_Law4016 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4016. -/
theorem noS8R164_Law4016 : ∀ v : Magma.tup8R164,
    ¬ @Equation4016 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4016) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4016) (by native_decide) v.1 v.2
    ((@Law4016.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4017 takes them (7 nodes). -/
def ordS8R164_Law4017 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4017. -/
theorem noS8R164_Law4017 : ∀ v : Magma.tup8R164,
    ¬ @Equation4017 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4017) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4017) (by native_decide) v.1 v.2
    ((@Law4017.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4018 takes them (10 nodes). -/
def ordS8R164_Law4018 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4018. -/
theorem noS8R164_Law4018 : ∀ v : Magma.tup8R164,
    ¬ @Equation4018 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4018) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4018) (by native_decide) v.1 v.2
    ((@Law4018.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4019 takes them (7 nodes). -/
def ordS8R164_Law4019 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4019. -/
theorem noS8R164_Law4019 : ∀ v : Magma.tup8R164,
    ¬ @Equation4019 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4019) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4019) (by native_decide) v.1 v.2
    ((@Law4019.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4020 takes them (7 nodes). -/
def ordS8R164_Law4020 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4020. -/
theorem noS8R164_Law4020 : ∀ v : Magma.tup8R164,
    ¬ @Equation4020 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4020) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4020) (by native_decide) v.1 v.2
    ((@Law4020.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4021 takes them (6 nodes). -/
def ordS8R164_Law4021 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4021. -/
theorem noS8R164_Law4021 : ∀ v : Magma.tup8R164,
    ¬ @Equation4021 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4021) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4021) (by native_decide) v.1 v.2
    ((@Law4021.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4022 takes them (6 nodes). -/
def ordS8R164_Law4022 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4022. -/
theorem noS8R164_Law4022 : ∀ v : Magma.tup8R164,
    ¬ @Equation4022 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4022) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4022) (by native_decide) v.1 v.2
    ((@Law4022.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4024 takes them (6 nodes). -/
def ordS8R164_Law4024 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4024. -/
theorem noS8R164_Law4024 : ∀ v : Magma.tup8R164,
    ¬ @Equation4024 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4024) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4024) (by native_decide) v.1 v.2
    ((@Law4024.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4025 takes them (6 nodes). -/
def ordS8R164_Law4025 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4025. -/
theorem noS8R164_Law4025 : ∀ v : Magma.tup8R164,
    ¬ @Equation4025 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4025) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4025) (by native_decide) v.1 v.2
    ((@Law4025.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4027 takes them (10 nodes). -/
def ordS8R164_Law4027 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4027. -/
theorem noS8R164_Law4027 : ∀ v : Magma.tup8R164,
    ¬ @Equation4027 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4027) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4027) (by native_decide) v.1 v.2
    ((@Law4027.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4028 takes them (7 nodes). -/
def ordS8R164_Law4028 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4028. -/
theorem noS8R164_Law4028 : ∀ v : Magma.tup8R164,
    ¬ @Equation4028 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4028) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4028) (by native_decide) v.1 v.2
    ((@Law4028.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4029 takes them (6 nodes). -/
def ordS8R164_Law4029 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4029. -/
theorem noS8R164_Law4029 : ∀ v : Magma.tup8R164,
    ¬ @Equation4029 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4029) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4029) (by native_decide) v.1 v.2
    ((@Law4029.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4030 takes them (6 nodes). -/
def ordS8R164_Law4030 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4030. -/
theorem noS8R164_Law4030 : ∀ v : Magma.tup8R164,
    ¬ @Equation4030 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4030) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4030) (by native_decide) v.1 v.2
    ((@Law4030.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4031 takes them (10 nodes). -/
def ordS8R164_Law4031 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4031. -/
theorem noS8R164_Law4031 : ∀ v : Magma.tup8R164,
    ¬ @Equation4031 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4031) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4031) (by native_decide) v.1 v.2
    ((@Law4031.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4032 takes them (6 nodes). -/
def ordS8R164_Law4032 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4032. -/
theorem noS8R164_Law4032 : ∀ v : Magma.tup8R164,
    ¬ @Equation4032 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4032) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law4032) (by native_decide) v.1 v.2
    ((@Law4032.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4033 takes them (6 nodes). -/
def ordS8R164_Law4033 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4033. -/
theorem noS8R164_Law4033 : ∀ v : Magma.tup8R164,
    ¬ @Equation4033 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4033) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4033) (by native_decide) v.1 v.2
    ((@Law4033.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4034 takes them (6 nodes). -/
def ordS8R164_Law4034 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4034. -/
theorem noS8R164_Law4034 : ∀ v : Magma.tup8R164,
    ¬ @Equation4034 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4034) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4034) (by native_decide) v.1 v.2
    ((@Law4034.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4035 takes them (10 nodes). -/
def ordS8R164_Law4035 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4035. -/
theorem noS8R164_Law4035 : ∀ v : Magma.tup8R164,
    ¬ @Equation4035 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4035) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4035) (by native_decide) v.1 v.2
    ((@Law4035.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4036 takes them (6 nodes). -/
def ordS8R164_Law4036 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4036. -/
theorem noS8R164_Law4036 : ∀ v : Magma.tup8R164,
    ¬ @Equation4036 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4036) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4036) (by native_decide) v.1 v.2
    ((@Law4036.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4037 takes them (6 nodes). -/
def ordS8R164_Law4037 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4037. -/
theorem noS8R164_Law4037 : ∀ v : Magma.tup8R164,
    ¬ @Equation4037 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4037) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4037) (by native_decide) v.1 v.2
    ((@Law4037.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4038 takes them (6 nodes). -/
def ordS8R164_Law4038 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4038. -/
theorem noS8R164_Law4038 : ∀ v : Magma.tup8R164,
    ¬ @Equation4038 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4038) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4038) (by native_decide) v.1 v.2
    ((@Law4038.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4039 takes them (6 nodes). -/
def ordS8R164_Law4039 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4039. -/
theorem noS8R164_Law4039 : ∀ v : Magma.tup8R164,
    ¬ @Equation4039 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4039) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4039) (by native_decide) v.1 v.2
    ((@Law4039.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (10 nodes). -/
def ordS8R164_Law4040 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4040. -/
theorem noS8R164_Law4040 : ∀ v : Magma.tup8R164,
    ¬ @Equation4040 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4041 takes them (6 nodes). -/
def ordS8R164_Law4041 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4041. -/
theorem noS8R164_Law4041 : ∀ v : Magma.tup8R164,
    ¬ @Equation4041 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4041) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4041) (by native_decide) v.1 v.2
    ((@Law4041.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4042 takes them (6 nodes). -/
def ordS8R164_Law4042 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4042. -/
theorem noS8R164_Law4042 : ∀ v : Magma.tup8R164,
    ¬ @Equation4042 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4042) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4042) (by native_decide) v.1 v.2
    ((@Law4042.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4043 takes them (6 nodes). -/
def ordS8R164_Law4043 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4043. -/
theorem noS8R164_Law4043 : ∀ v : Magma.tup8R164,
    ¬ @Equation4043 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4043) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4043) (by native_decide) v.1 v.2
    ((@Law4043.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4044 takes them (7 nodes). -/
def ordS8R164_Law4044 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4044. -/
theorem noS8R164_Law4044 : ∀ v : Magma.tup8R164,
    ¬ @Equation4044 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4044) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4044) (by native_decide) v.1 v.2
    ((@Law4044.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4045 takes them (10 nodes). -/
def ordS8R164_Law4045 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4045. -/
theorem noS8R164_Law4045 : ∀ v : Magma.tup8R164,
    ¬ @Equation4045 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4045) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4045) (by native_decide) v.1 v.2
    ((@Law4045.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4046 takes them (7 nodes). -/
def ordS8R164_Law4046 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4046. -/
theorem noS8R164_Law4046 : ∀ v : Magma.tup8R164,
    ¬ @Equation4046 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4046) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4046) (by native_decide) v.1 v.2
    ((@Law4046.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4047 takes them (7 nodes). -/
def ordS8R164_Law4047 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4047. -/
theorem noS8R164_Law4047 : ∀ v : Magma.tup8R164,
    ¬ @Equation4047 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4047) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4047) (by native_decide) v.1 v.2
    ((@Law4047.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4048 takes them (6 nodes). -/
def ordS8R164_Law4048 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4048. -/
theorem noS8R164_Law4048 : ∀ v : Magma.tup8R164,
    ¬ @Equation4048 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4048) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4048) (by native_decide) v.1 v.2
    ((@Law4048.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4049 takes them (6 nodes). -/
def ordS8R164_Law4049 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4049. -/
theorem noS8R164_Law4049 : ∀ v : Magma.tup8R164,
    ¬ @Equation4049 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4049) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4049) (by native_decide) v.1 v.2
    ((@Law4049.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4050 takes them (10 nodes). -/
def ordS8R164_Law4050 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4050. -/
theorem noS8R164_Law4050 : ∀ v : Magma.tup8R164,
    ¬ @Equation4050 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4050) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4050) (by native_decide) v.1 v.2
    ((@Law4050.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4051 takes them (6 nodes). -/
def ordS8R164_Law4051 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4051. -/
theorem noS8R164_Law4051 : ∀ v : Magma.tup8R164,
    ¬ @Equation4051 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4051) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4051) (by native_decide) v.1 v.2
    ((@Law4051.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4052 takes them (6 nodes). -/
def ordS8R164_Law4052 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4052. -/
theorem noS8R164_Law4052 : ∀ v : Magma.tup8R164,
    ¬ @Equation4052 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4052) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4052) (by native_decide) v.1 v.2
    ((@Law4052.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4053 takes them (6 nodes). -/
def ordS8R164_Law4053 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4053. -/
theorem noS8R164_Law4053 : ∀ v : Magma.tup8R164,
    ¬ @Equation4053 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4053) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4053) (by native_decide) v.1 v.2
    ((@Law4053.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4054 takes them (6 nodes). -/
def ordS8R164_Law4054 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4054. -/
theorem noS8R164_Law4054 : ∀ v : Magma.tup8R164,
    ¬ @Equation4054 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4054) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4054) (by native_decide) v.1 v.2
    ((@Law4054.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4055 takes them (10 nodes). -/
def ordS8R164_Law4055 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4055. -/
theorem noS8R164_Law4055 : ∀ v : Magma.tup8R164,
    ¬ @Equation4055 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4055) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4055) (by native_decide) v.1 v.2
    ((@Law4055.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4056 takes them (6 nodes). -/
def ordS8R164_Law4056 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4056. -/
theorem noS8R164_Law4056 : ∀ v : Magma.tup8R164,
    ¬ @Equation4056 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4056) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4056) (by native_decide) v.1 v.2
    ((@Law4056.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4057 takes them (6 nodes). -/
def ordS8R164_Law4057 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4057. -/
theorem noS8R164_Law4057 : ∀ v : Magma.tup8R164,
    ¬ @Equation4057 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4057) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4057) (by native_decide) v.1 v.2
    ((@Law4057.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4058 takes them (6 nodes). -/
def ordS8R164_Law4058 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4058. -/
theorem noS8R164_Law4058 : ∀ v : Magma.tup8R164,
    ¬ @Equation4058 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4058) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4058) (by native_decide) v.1 v.2
    ((@Law4058.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4059 takes them (6 nodes). -/
def ordS8R164_Law4059 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4059. -/
theorem noS8R164_Law4059 : ∀ v : Magma.tup8R164,
    ¬ @Equation4059 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4059) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4059) (by native_decide) v.1 v.2
    ((@Law4059.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4060 takes them (10 nodes). -/
def ordS8R164_Law4060 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4060. -/
theorem noS8R164_Law4060 : ∀ v : Magma.tup8R164,
    ¬ @Equation4060 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4060) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4060) (by native_decide) v.1 v.2
    ((@Law4060.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `84` equations. -/
theorem srch8R164_refutes_10 :
    FamilyRefutes Magma.srch8R164 [
      3969, 3970, 3971, 3972, 3974, 3975, 3976, 3977, 3978, 3980, 3981, 3982, 3983, 3984, 3985,
      3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3995, 3996, 3998, 3999, 4000, 4001, 4002,
      4003, 4004, 4005, 4006, 4008, 4009, 4010, 4011, 4012, 4014, 4015, 4016, 4017, 4018, 4019,
      4020, 4021, 4022, 4024, 4025, 4027, 4028, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4036,
      4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051,
      4052, 4053, 4054, 4055, 4056, 4057, 4058, 4059, 4060
    ] :=
  ⟨noS8R164_Law3969, noS8R164_Law3970, noS8R164_Law3971, noS8R164_Law3972, noS8R164_Law3974, noS8R164_Law3975, noS8R164_Law3976, noS8R164_Law3977, noS8R164_Law3978, noS8R164_Law3980, noS8R164_Law3981, noS8R164_Law3982, noS8R164_Law3983, noS8R164_Law3984, noS8R164_Law3985, noS8R164_Law3986, noS8R164_Law3987, noS8R164_Law3988, noS8R164_Law3989, noS8R164_Law3990, noS8R164_Law3991, noS8R164_Law3992, noS8R164_Law3993, noS8R164_Law3995, noS8R164_Law3996, noS8R164_Law3998, noS8R164_Law3999, noS8R164_Law4000, noS8R164_Law4001, noS8R164_Law4002, noS8R164_Law4003, noS8R164_Law4004, noS8R164_Law4005, noS8R164_Law4006, noS8R164_Law4008, noS8R164_Law4009, noS8R164_Law4010, noS8R164_Law4011, noS8R164_Law4012, noS8R164_Law4014, noS8R164_Law4015, noS8R164_Law4016, noS8R164_Law4017, noS8R164_Law4018, noS8R164_Law4019, noS8R164_Law4020, noS8R164_Law4021, noS8R164_Law4022, noS8R164_Law4024, noS8R164_Law4025, noS8R164_Law4027, noS8R164_Law4028, noS8R164_Law4029, noS8R164_Law4030, noS8R164_Law4031, noS8R164_Law4032, noS8R164_Law4033, noS8R164_Law4034, noS8R164_Law4035, noS8R164_Law4036, noS8R164_Law4037, noS8R164_Law4038, noS8R164_Law4039, noS8R164_Law4040, noS8R164_Law4041, noS8R164_Law4042, noS8R164_Law4043, noS8R164_Law4044, noS8R164_Law4045, noS8R164_Law4046, noS8R164_Law4047, noS8R164_Law4048, noS8R164_Law4049, noS8R164_Law4050, noS8R164_Law4051, noS8R164_Law4052, noS8R164_Law4053, noS8R164_Law4054, noS8R164_Law4055, noS8R164_Law4056, noS8R164_Law4057, noS8R164_Law4058, noS8R164_Law4059, noS8R164_Law4060⟩
