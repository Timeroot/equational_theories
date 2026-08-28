import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 22 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `21`
equations here, 2,770 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2119 takes them (56 nodes). -/
def ordS6A_Law2119 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2119. -/
theorem noS6A_Law2119 : ∀ v : Magma.tupS6A,
    ¬ @Equation2119 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2119) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2119) (by native_decide) v.1 v.2
    ((@Law2119.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2127 takes them (108 nodes). -/
def ordS6A_Law2127 : List (Fin 11) := [9, 10, 4, 8, 5, 0, 2, 1, 6, 7, 3]

/-- No member of the class satisfies equation 2127. -/
theorem noS6A_Law2127 : ∀ v : Magma.tupS6A,
    ¬ @Equation2127 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2127) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2127) (by native_decide) v.1 v.2
    ((@Law2127.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2130 takes them (153 nodes). -/
def ordS6A_Law2130 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2130. -/
theorem noS6A_Law2130 : ∀ v : Magma.tupS6A,
    ¬ @Equation2130 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2130) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2130) (by native_decide) v.1 v.2
    ((@Law2130.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2140 takes them (125 nodes). -/
def ordS6A_Law2140 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2140. -/
theorem noS6A_Law2140 : ∀ v : Magma.tupS6A,
    ¬ @Equation2140 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2140) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2140) (by native_decide) v.1 v.2
    ((@Law2140.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2144 takes them (346 nodes). -/
def ordS6A_Law2144 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2144. -/
theorem noS6A_Law2144 : ∀ v : Magma.tupS6A,
    ¬ @Equation2144 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2144) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2144) (by native_decide) v.1 v.2
    ((@Law2144.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2148 takes them (127 nodes). -/
def ordS6A_Law2148 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2148. -/
theorem noS6A_Law2148 : ∀ v : Magma.tupS6A,
    ¬ @Equation2148 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2148) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2148) (by native_decide) v.1 v.2
    ((@Law2148.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2156 takes them (125 nodes). -/
def ordS6A_Law2156 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2156. -/
theorem noS6A_Law2156 : ∀ v : Magma.tupS6A,
    ¬ @Equation2156 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2156) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2156) (by native_decide) v.1 v.2
    ((@Law2156.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2165 takes them (88 nodes). -/
def ordS6A_Law2165 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2165. -/
theorem noS6A_Law2165 : ∀ v : Magma.tupS6A,
    ¬ @Equation2165 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2165) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2165) (by native_decide) v.1 v.2
    ((@Law2165.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2169 takes them (142 nodes). -/
def ordS6A_Law2169 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2169. -/
theorem noS6A_Law2169 : ∀ v : Magma.tupS6A,
    ¬ @Equation2169 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2169) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2169) (by native_decide) v.1 v.2
    ((@Law2169.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2173 takes them (61 nodes). -/
def ordS6A_Law2173 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2173. -/
theorem noS6A_Law2173 : ∀ v : Magma.tupS6A,
    ¬ @Equation2173 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2173) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2173) (by native_decide) v.1 v.2
    ((@Law2173.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2178 takes them (326 nodes). -/
def ordS6A_Law2178 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2178. -/
theorem noS6A_Law2178 : ∀ v : Magma.tupS6A,
    ¬ @Equation2178 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2178) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2178) (by native_decide) v.1 v.2
    ((@Law2178.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2186 takes them (170 nodes). -/
def ordS6A_Law2186 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2186. -/
theorem noS6A_Law2186 : ∀ v : Magma.tupS6A,
    ¬ @Equation2186 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2186) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2186) (by native_decide) v.1 v.2
    ((@Law2186.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2190 takes them (93 nodes). -/
def ordS6A_Law2190 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2190. -/
theorem noS6A_Law2190 : ∀ v : Magma.tupS6A,
    ¬ @Equation2190 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2190) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2190) (by native_decide) v.1 v.2
    ((@Law2190.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2195 takes them (223 nodes). -/
def ordS6A_Law2195 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2195. -/
theorem noS6A_Law2195 : ∀ v : Magma.tupS6A,
    ¬ @Equation2195 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2195) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2195) (by native_decide) v.1 v.2
    ((@Law2195.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2199 takes them (125 nodes). -/
def ordS6A_Law2199 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2199. -/
theorem noS6A_Law2199 : ∀ v : Magma.tupS6A,
    ¬ @Equation2199 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2199) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2199) (by native_decide) v.1 v.2
    ((@Law2199.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2207 takes them (47 nodes). -/
def ordS6A_Law2207 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2207. -/
theorem noS6A_Law2207 : ∀ v : Magma.tupS6A,
    ¬ @Equation2207 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2207) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2207) (by native_decide) v.1 v.2
    ((@Law2207.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2212 takes them (141 nodes). -/
def ordS6A_Law2212 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2212. -/
theorem noS6A_Law2212 : ∀ v : Magma.tupS6A,
    ¬ @Equation2212 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2212) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2212) (by native_decide) v.1 v.2
    ((@Law2212.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2217 takes them (48 nodes). -/
def ordS6A_Law2217 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2217. -/
theorem noS6A_Law2217 : ∀ v : Magma.tupS6A,
    ¬ @Equation2217 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2217) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2217) (by native_decide) v.1 v.2
    ((@Law2217.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2222 takes them (76 nodes). -/
def ordS6A_Law2222 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2222. -/
theorem noS6A_Law2222 : ∀ v : Magma.tupS6A,
    ¬ @Equation2222 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2222) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2222) (by native_decide) v.1 v.2
    ((@Law2222.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2232 takes them (43 nodes). -/
def ordS6A_Law2232 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2232. -/
theorem noS6A_Law2232 : ∀ v : Magma.tupS6A,
    ¬ @Equation2232 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2232) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2232) (by native_decide) v.1 v.2
    ((@Law2232.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2239 takes them (147 nodes). -/
def ordS6A_Law2239 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2239. -/
theorem noS6A_Law2239 : ∀ v : Magma.tupS6A,
    ¬ @Equation2239 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2239) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2239) (by native_decide) v.1 v.2
    ((@Law2239.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `21` equations. -/
theorem srch6A_refutes_21 :
    FamilyRefutes Magma.srch6A [
      2119, 2127, 2130, 2140, 2144, 2148, 2156, 2165, 2169, 2173, 2178, 2186, 2190, 2195, 2199,
      2207, 2212, 2217, 2222, 2232, 2239
    ] :=
  ⟨noS6A_Law2119, noS6A_Law2127, noS6A_Law2130, noS6A_Law2140, noS6A_Law2144, noS6A_Law2148, noS6A_Law2156, noS6A_Law2165, noS6A_Law2169, noS6A_Law2173, noS6A_Law2178, noS6A_Law2186, noS6A_Law2190, noS6A_Law2195, noS6A_Law2199, noS6A_Law2207, noS6A_Law2212, noS6A_Law2217, noS6A_Law2222, noS6A_Law2232, noS6A_Law2239⟩
