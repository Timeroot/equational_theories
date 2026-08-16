import equational_theories.DecideBang
import equational_theories.Definability.CertSyntax
import equational_theories.Definability.Negative

/-!
# The symmetry certificates

`Definability/Negative.lean` proves the *obstructions*: if `L` is definable from `L'` and `L'` has
a model on `Fin n` with a prescribed symmetry, then `L` has a model on `Fin n` with (at least) the
same symmetry, and the classification lemmas there cut that down to a short explicit family of
magmas. This file packages each obstruction as a single lemma of the shape

  "`M` is a member of the family and satisfies `L'`" + "no member of the family satisfies `L`"
  ⟹ `¬ L.DefinableFrom L'`,

and `Definability/Certs/` records, for each family, exactly which of the `4694` equations are
satisfied by some member (the **sources**) and which are satisfied by none (the **targets**).
Those two lists are complementary, and every (target, source) pair is a non-definability fact.

| family | carrier | size | sources | targets | pairs |
| --- | --- | --- | --- | --- | --- |
| `Magma.fin2` — all magmas | `Fin 2` | `16` | `3136` | `1558` | `4885888` |
| `Magma.fin2Unary` — `x ↦ x + 1` an automorphism | `Fin 2` | `4` | `2075` | `2619` | `5434425` |
| `Magma.cyclic3` — `x ↦ x + 1` an automorphism | `Fin 3` | `27` | `2248` | `2446` | `5498608` |
| `Magma.cyclic4` — `x ↦ x + 1` an automorphism | `Fin 4` | `256` | `2085` | `2609` | `5439765` |
| `Magma.reflective3` — `x ↦ -x` an automorphism | `Fin 3` | `81` | `3102` | `1592` | `4938384` |
| `Magma.affine3` — all of `S₃` automorphisms | `Fin 3` | `3` | `2222` | `2472` | `5492784` |
| `Magma.affine5` — all of `AGL(1, 5)` automorphisms | `Fin 5` | `5` | `2223` | `2471` | `5493033` |
| `Magma.affine7` — all of `AGL(1, 7)` automorphisms | `Fin 7` | `7` | `2181` | `2166` | `4724046` |
| `Magma.alt4` — all of `A₄` automorphisms | `Fin 4` | `4` | `2121` | `2226` | `4721346` |
| `Magma.affine8` — all of `AGL(1, 8)` automorphisms | `Fin 8` | `8` | `2101` | `2246` | `4718846` |

All of them refute full first-order definability, since they only ever use *invertible* symmetries
(for `Magma.fin2` there is no symmetry at all, just the cardinality of the carrier).

The last three families list only the `4347` equations in at most four variables: `decide` costs
`n ^ v` per equation on `Fin n`, which is what makes the larger carriers expensive, and the closed
rectangle of every family here is unchanged by dropping the five- and six-variable equations, each
of which is sandwiched between four-variable ones in the implication order.

The `Satisfies` and `FamilyRefutes` statements are plain conjunctions, in the same spirit as the
`Facts` lists of `Generated/`; a single pair is extracted from them by projection, see
`Definability/Certs/Examples.lean`.
-/

open Law Law.MagmaLaw

namespace Magma

/-! ### The families -/

/-- All `16` magmas on `Fin 2`, parametrized by the four entries of the multiplication table. -/
@[implicit_reducible]
def fin2 (a b c d : Fin 2) : Magma (Fin 2) :=
  Magma.mk fun
    | 0, 0 => a
    | 0, 1 => b
    | 1, 0 => c
    | 1, 1 => d

theorem fin2_op_self (M : Magma (Fin 2)) :
    fin2 (M.op 0 0) (M.op 0 1) (M.op 1 0) (M.op 1 1) = M := by
  obtain ⟨op⟩ := M
  have hop : (fin2 (op 0 0) (op 0 1) (op 1 0) (op 1 1)).op = op := by
    funext x y
    fin_cases x <;> fin_cases y <;> rfl
  exact congrArg Magma.mk hop

/-- The `4` magmas on `Fin 2` admitting the nontrivial permutation `x ↦ x + 1` as an automorphism;
by `Magma.isEndo_swap_iff` these are exactly the operations that ignore one argument. -/
@[implicit_reducible]
def fin2Unary : Fin 4 → Magma (Fin 2)
  | 0 => Magma.mk fun x _ ↦ x
  | 1 => Magma.mk fun _ y ↦ y
  | 2 => Magma.mk fun x _ ↦ x + 1
  | 3 => Magma.mk fun _ y ↦ y + 1

theorem fin2Unary_isEndo_swap (i : Fin 4) : (fin2Unary i).IsEndo ⇑Fin.swap2 := by
  revert i; decide

/-- The `27` magmas on `Fin 3` admitting the cyclic shift `x ↦ x + 1` as an automorphism; by
`Magma.op_eq_of_isEndo_add_one` these are exactly the magmas determined by their first row. -/
@[implicit_reducible]
def cyclic3 (a b c : Fin 3) : Magma (Fin 3) := Magma.mk fun x y ↦ ![a, b, c] (y - x) + x

theorem cyclic3_isEndo_addRight (a b c : Fin 3) :
    (cyclic3 a b c).IsEndo ⇑(Equiv.addRight (1 : Fin 3)) := by
  revert a b c; decide

/-- The `256` magmas on `Fin 4` admitting the cyclic shift `x ↦ x + 1` as an automorphism; by
`Magma.op_eq_of_isEndo_add_one` these too are exactly the magmas determined by their first row. -/
@[implicit_reducible]
def cyclic4 (a b c d : Fin 4) : Magma (Fin 4) := Magma.mk fun x y ↦ ![a, b, c, d] (y - x) + x

theorem cyclic4_isEndo_addRight (a b c d : Fin 4) :
    (cyclic4 a b c d).IsEndo ⇑(Equiv.addRight (1 : Fin 4)) := by
  revert a b c d; decide

/-- The `81` magmas on `Fin 3` admitting the reflection `x ↦ -x` as an automorphism; see
`Magma.op_eq_reflOp3`. -/
@[implicit_reducible]
def reflective3 (a b c d : Fin 3) : Magma (Fin 3) := Magma.mk (reflOp3 a b c d)

theorem reflective3_isEndo_neg (a b c d : Fin 3) :
    (reflective3 a b c d).IsEndo ⇑(Equiv.neg (Fin 3)) := by
  revert a b c d; decide

/-- The `3` magmas on `Fin 3` admitting all of `S₃` as automorphisms; see
`Magma.op_eq_of_isEndo_add_one_neg`. -/
@[implicit_reducible]
def affine3 (c : Fin 3) : Magma (Fin 3) := Magma.mk fun x y ↦ c * (y - x) + x

theorem affine3_isEndo_addRight (c : Fin 3) :
    (affine3 c).IsEndo ⇑(Equiv.addRight (1 : Fin 3)) := by
  revert c; decide

theorem affine3_isEndo_neg (c : Fin 3) : (affine3 c).IsEndo ⇑(Equiv.neg (Fin 3)) := by
  revert c; decide

/-- The `5` magmas on `Fin 5` admitting all of `F₂₀ = AGL(1, 5)` as automorphisms; see
`Magma.op_eq_of_isEndo_add_one_double`. -/
@[implicit_reducible]
def affine5 (c : Fin 5) : Magma (Fin 5) := Magma.mk fun x y ↦ c * (y - x) + x

theorem affine5_isEndo_addRight (c : Fin 5) :
    (affine5 c).IsEndo ⇑(Equiv.addRight (1 : Fin 5)) := by
  revert c; decide

theorem affine5_isEndo_double (c : Fin 5) : (affine5 c).IsEndo ⇑Fin.double5 := by
  revert c; decide

/-- The `7` magmas on `Fin 7` admitting all of `F₄₂ = AGL(1, 7)` as automorphisms; see
`Magma.op_eq_of_isEndo_add_one_triple`. -/
@[implicit_reducible]
def affine7 (c : Fin 7) : Magma (Fin 7) := Magma.mk fun x y ↦ c * (y - x) + x

theorem affine7_isEndo_addRight (c : Fin 7) :
    (affine7 c).IsEndo ⇑(Equiv.addRight (1 : Fin 7)) := by
  revert c; decide

theorem affine7_isEndo_triple (c : Fin 7) : (affine7 c).IsEndo ⇑Fin.triple7 := by
  revert c; decide

/-- The `4` magmas on `Fin 4` admitting the alternating group `A₄` as automorphisms; see
`Magma.op_eq_a4Op`. -/
@[implicit_reducible]
def alt4 (c : Fin 4) : Magma (Fin 4) := Magma.mk (a4Op c)

theorem alt4_isEndo_xor1 (c : Fin 4) : (alt4 c).IsEndo ⇑(Fin.xorPerm4 1) := by
  revert c; decide

theorem alt4_isEndo_xor2 (c : Fin 4) : (alt4 c).IsEndo ⇑(Fin.xorPerm4 2) := by
  revert c; decide

theorem alt4_isEndo_rot (c : Fin 4) : (alt4 c).IsEndo ⇑Fin.rot4 := by
  revert c; decide

/-- The `8` magmas on `Fin 8` admitting all of `AGL(1, 8)` as automorphisms; see
`Magma.op_eq_a8Op`. -/
@[implicit_reducible]
def affine8 (c : Fin 8) : Magma (Fin 8) := Magma.mk (a8Op c)

theorem affine8_isEndo_xor1 (c : Fin 8) : (affine8 c).IsEndo ⇑(Fin.xorPerm8 1) := by
  revert c; decide

theorem affine8_isEndo_xor2 (c : Fin 8) : (affine8 c).IsEndo ⇑(Fin.xorPerm8 2) := by
  revert c; decide

theorem affine8_isEndo_xor4 (c : Fin 8) : (affine8 c).IsEndo ⇑(Fin.xorPerm8 4) := by
  revert c; decide

theorem affine8_isEndo_double (c : Fin 8) : (affine8 c).IsEndo ⇑Fin.double8 := by
  revert c; decide

end Magma

namespace Law.MagmaLaw

variable {L L' : Law.NatMagmaLaw}

/-! ### The certificates -/

/-- **Cardinality certificate on `Fin 2`.** If `L'` has a two-element model and `L` has none, then
`L` is not definable from `L'`. -/
theorem not_definableFrom_fin2 {a b c d : Fin 2}
    (hsrc : @satisfies _ (Fin 2) (Magma.fin2 a b c d) L')
    (htgt : ∀ a b c d : Fin 2, ¬ @satisfies _ (Fin 2) (Magma.fin2 a b c d) L) :
    ¬ L.DefinableFrom L' := by
  refine not_definableFrom_of_no_model (Magma.fin2 a b c d) hsrc fun M' hM' ↦ ?_
  refine htgt (M'.op 0 0) (M'.op 0 1) (M'.op 1 0) (M'.op 1 1) ?_
  rw [Magma.fin2_op_self]
  exact hM'

/-- **Two-element symmetry certificate.** If `L'` has a two-element model on which `x ↦ x + 1` is
an automorphism, then any law definable from `L'` is satisfied by one of the four magmas
`Magma.fin2Unary i`. -/
theorem not_definableFrom_fin2Unary {i : Fin 4}
    (hsrc : @satisfies _ (Fin 2) (Magma.fin2Unary i) L')
    (htgt : ∀ i : Fin 4, ¬ @satisfies _ (Fin 2) (Magma.fin2Unary i) L) :
    ¬ L.DefinableFrom L' := by
  intro h
  obtain ⟨op, hop, hsat⟩ :=
    exists_fin2_model_of_definableFrom (Magma.fin2Unary i) hsrc (Magma.fin2Unary_isEndo_swap i) h
  rcases hop with rfl | rfl | rfl | rfl
  exacts [htgt 0 hsat, htgt 1 hsat, htgt 2 hsat, htgt 3 hsat]

/-- **Cyclic certificate on `Fin 3`.** If `L'` has a model on `Fin 3` on which the cyclic shift is
an automorphism, then any law definable from `L'` is satisfied by one of the `27` magmas
`Magma.cyclic3 a b c`. -/
theorem not_definableFrom_cyclic3 {a b c : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.cyclic3 a b c) L')
    (htgt : ∀ a b c : Fin 3, ¬ @satisfies _ (Fin 3) (Magma.cyclic3 a b c) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨a', b', c', hg⟩ := exists_cyclic3_model_of_definableFrom (Magma.cyclic3 a b c) hsrc
    (Magma.cyclic3_isEndo_addRight a b c) h
  htgt a' b' c' hg

/-- **Cyclic certificate on `Fin 4`.** If `L'` has a model on `Fin 4` on which `x ↦ x + 1` is an
automorphism, then any law definable from `L'` is satisfied by one of the `256` magmas
`Magma.cyclic4 a b c d`. -/
theorem not_definableFrom_cyclic4 {a b c d : Fin 4}
    (hsrc : @satisfies _ (Fin 4) (Magma.cyclic4 a b c d) L')
    (htgt : ∀ a b c d : Fin 4, ¬ @satisfies _ (Fin 4) (Magma.cyclic4 a b c d) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨a', b', c', d', hg⟩ := exists_cyclic4_model_of_definableFrom (Magma.cyclic4 a b c d) hsrc
    (Magma.cyclic4_isEndo_addRight a b c d) h
  htgt a' b' c' d' hg

/-- **Reflection certificate on `Fin 3`.** If `L'` has a model on `Fin 3` on which `x ↦ -x` is an
automorphism, then any law definable from `L'` is satisfied by one of the `81` magmas
`Magma.reflective3 a b c d`. -/
theorem not_definableFrom_reflective3 {a b c d : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.reflective3 a b c d) L')
    (htgt : ∀ a b c d : Fin 3, ¬ @satisfies _ (Fin 3) (Magma.reflective3 a b c d) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨a', b', c', d', hg⟩ := exists_reflective3_model_of_definableFrom (Magma.reflective3 a b c d)
    hsrc (Magma.reflective3_isEndo_neg a b c d) h
  htgt a' b' c' d' hg

/-- **Full symmetry certificate on `Fin 3`.** If `L'` has a model on `Fin 3` with all of `S₃` as
automorphisms, then any law definable from `L'` is satisfied by one of the `3` affine magmas. -/
theorem not_definableFrom_affine3 {c : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.affine3 c) L')
    (htgt : ∀ c : Fin 3, ¬ @satisfies _ (Fin 3) (Magma.affine3 c) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨c', hg⟩ := exists_affine3_model_of_definableFrom (Magma.affine3 c) hsrc
    (Magma.affine3_isEndo_addRight c) (Magma.affine3_isEndo_neg c) h
  htgt c' hg

/-- **Full symmetry certificate on `Fin 5`.** If `L'` has a model on `Fin 5` with all of
`F₂₀ = AGL(1, 5)` as automorphisms, then any law definable from `L'` is satisfied by one of the `5`
affine magmas. -/
theorem not_definableFrom_affine5 {c : Fin 5}
    (hsrc : @satisfies _ (Fin 5) (Magma.affine5 c) L')
    (htgt : ∀ c : Fin 5, ¬ @satisfies _ (Fin 5) (Magma.affine5 c) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨c', hg⟩ := exists_affine5_model_of_definableFrom (Magma.affine5 c) hsrc
    (Magma.affine5_isEndo_addRight c) (Magma.affine5_isEndo_double c) h
  htgt c' hg

/-- **Full symmetry certificate on `Fin 7`.** If `L'` has a model on `Fin 7` with all of
`F₄₂ = AGL(1, 7)` as automorphisms, then any law definable from `L'` is satisfied by one of the `7`
affine magmas. -/
theorem not_definableFrom_affine7 {c : Fin 7}
    (hsrc : @satisfies _ (Fin 7) (Magma.affine7 c) L')
    (htgt : ∀ c : Fin 7, ¬ @satisfies _ (Fin 7) (Magma.affine7 c) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨c', hg⟩ := exists_affine7_model_of_definableFrom (Magma.affine7 c) hsrc
    (Magma.affine7_isEndo_addRight c) (Magma.affine7_isEndo_triple c) h
  htgt c' hg

/-- **Alternating certificate on `Fin 4`.** If `L'` has a model on `Fin 4` with all of `A₄` as
automorphisms, then any law definable from `L'` is satisfied by one of the `4` magmas
`Magma.alt4 c`. -/
theorem not_definableFrom_alt4 {c : Fin 4}
    (hsrc : @satisfies _ (Fin 4) (Magma.alt4 c) L')
    (htgt : ∀ c : Fin 4, ¬ @satisfies _ (Fin 4) (Magma.alt4 c) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨c', hg⟩ := exists_alt4_model_of_definableFrom (Magma.alt4 c) hsrc
    (Magma.alt4_isEndo_xor1 c) (Magma.alt4_isEndo_xor2 c) (Magma.alt4_isEndo_rot c) h
  htgt c' hg

/-- **Full symmetry certificate on `Fin 8`.** If `L'` has a model on `Fin 8` with all of
`AGL(1, 8)` as automorphisms, then any law definable from `L'` is satisfied by one of the `8`
affine magmas `Magma.affine8 c`. -/
theorem not_definableFrom_affine8 {c : Fin 8}
    (hsrc : @satisfies _ (Fin 8) (Magma.affine8 c) L')
    (htgt : ∀ c : Fin 8, ¬ @satisfies _ (Fin 8) (Magma.affine8 c) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨c', hg⟩ := exists_affine8_model_of_definableFrom (Magma.affine8 c) hsrc
    (Magma.affine8_isEndo_xor1 c) (Magma.affine8_isEndo_xor2 c) (Magma.affine8_isEndo_xor4 c)
    (Magma.affine8_isEndo_double c) h
  htgt c' hg

end Law.MagmaLaw
