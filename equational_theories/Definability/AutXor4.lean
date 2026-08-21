import equational_theories.Definability.Negative
import equational_theories.Equations.All

/-!
# Four-element carriers with one double transposition

`Definability/Negative.lean` develops the symmetry obstruction and applies it to the *large*
symmetry groups: the cyclic shift, the reflection, `A₄`, `AGL(1, 5)`. Those give very small
families -- four operations on `Fin 4` for `A₄` -- but they also demand a very symmetric model of
the source, and most of the definability board has none.

This file goes to the other extreme: a single nontrivial automorphism, the double transposition
`x ↦ x ⊕ 1` of `Fin 4`. The hypothesis is cheap, and the price is that the family of invariant
operations has `4 ^ 8 = 65536` members rather than four. Nothing is written down. `Magma.xorOp4`
describes the family by a formula -- an invariant operation is free on the two rows `0 ◇ -` and
`2 ◇ -`, and the other two rows are forced -- so refuting a target is one `native_decide` over a
pair of functions `Fin 4 → Fin 4`, in the style of `Definability/RegularCover.lean`.

The classification is the whole content. Writing `s` for `x ↦ x ⊕ 1`, an automorphism satisfies
`s (x ◇ y) = s x ◇ s y`, so row `1 = s 0` is determined by row `0` and row `3 = s 2` by row `2`,
and there is no further constraint: the orbits of `⟨s⟩` on ordered pairs all have size two and
trivial stabilizer, so every one of the `4 ^ 8` choices really does occur.

Unlike a clone certificate, which bounds the *term* operations, this bounds the first-order
definable ones as well -- `Magma.IsEndo.of_definable` -- so each theorem here refutes
`DefinableFrom`, the strongest of the four relations on the board. The witnesses are finite, so the
finite-carrier flavours follow as well.

## Contents

* `Magma.xorOp4`, `Magma.op_eq_xorOp4` -- the family and the classification;
* `Law.MagmaLaw.not_definableFrom_xorOp4` -- the three hypotheses a cell needs;
* `noXorOp4_LawN` -- one per target: no invariant operation satisfies it;
* `xorM<n>` -- one per source: a four-element model with the symmetry;
* the refutations themselves, one line each.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma

/-- The operations on `Fin 4` invariant under the double transposition `x ↦ x ⊕ 1`, parametrized
by the two free rows `r₀ = 0 ◇ -` and `r₂ = 2 ◇ -`. Rows `1` and `3` are the images of those two
under the symmetry. See `Magma.op_eq_xorOp4`. -/
def xorOp4 (r₀ r₂ : Fin 4 → Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, y => r₀ y
  | 1, y => Fin.xor4 1 (r₀ (Fin.xor4 1 y))
  | 2, y => r₂ y
  | 3, y => Fin.xor4 1 (r₂ (Fin.xor4 1 y))

/-- Every magma on `Fin 4` admitting `x ↦ x ⊕ 1` as an endomorphism is one of the `65536` magmas
`Magma.xorOp4 r₀ r₂`. -/
theorem op_eq_xorOp4 {M : Magma (Fin 4)} (h : M.IsEndo (Fin.xor4 1)) :
    M.op = xorOp4 (M.op 0) (M.op 2) := by
  have key : ∀ x y : Fin 4,
      M.op (Fin.xor4 1 x) y = Fin.xor4 1 (M.op x (Fin.xor4 1 y)) := by
    intro x y
    have := h x (Fin.xor4 1 y)
    rw [Fin.xor4_self] at this
    exact this.symm
  funext x y
  fin_cases x
  · rfl
  · exact key 0 y
  · rfl
  · exact key 2 y

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- If `L'` has a four-element model admitting `x ↦ x ⊕ 1` as an automorphism, then any law
definable from `L'` is satisfied by one of the `65536` magmas `Magma.xorOp4 r₀ r₂`. -/
theorem exists_xorOp4_model_of_definableFrom (M : Magma (Fin 4)) (hM : satisfies (Fin 4) L')
    (hx : M.IsEndo (Fin.xor4 1)) (h : L.DefinableFrom L') :
    ∃ r₀ r₂ : Fin 4 → Fin 4, @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  have he : M'.IsEndo (Fin.xor4 1) :=
    Magma.IsEndo.of_definable (e := Fin.xorPerm4 1) hd hx
  refine ⟨M'.op 0, M'.op 2, ?_⟩
  have key : (Magma.mk (Magma.xorOp4 (M'.op 0) (M'.op 2))) = M' := by
    cases M' with
    | mk op => exact congrArg Magma.mk (Magma.op_eq_xorOp4 (M := Magma.mk op) he).symm
  rw [key]
  exact hM'

/-- The three hypotheses a cell needs: a four-element model of the source, its symmetry, and the
`native_decide` that no invariant operation satisfies the target. -/
theorem not_definableFrom_xorOp4 (M : Magma (Fin 4)) (hM : satisfies (Fin 4) L')
    (hx : M.IsEndo (Fin.xor4 1))
    (hL : ∀ r₀ r₂ : Fin 4 → Fin 4, ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) L) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨r₀, r₂, hg⟩ := exists_xorOp4_model_of_definableFrom M hM hx h
  hL r₀ r₂ hg

end Law.MagmaLaw

/-! ### The targets

For each target, no operation on `Fin 4` commuting with `x ↦ x ⊕ 1` satisfies it. Each
check ranges over the `65536` pairs of free rows; the targets here have at most three
variables, so the whole enumeration is a few million evaluations.
-/

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 2 (2 variables). -/
theorem noXorOp4_Law2 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law2 := by
  simp only [Law2.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 40 (2 variables). -/
theorem noXorOp4_Law40 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law40 := by
  simp only [Law40.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 43 (2 variables). -/
theorem noXorOp4_Law43 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law43 := by
  simp only [Law43.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 63 (2 variables). -/
theorem noXorOp4_Law63 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law63 := by
  simp only [Law63.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 332 (2 variables). -/
theorem noXorOp4_Law332 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law332 := by
  simp only [Law332.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 464 (2 variables). -/
theorem noXorOp4_Law464 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law464 := by
  simp only [Law464.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 467 (2 variables). -/
theorem noXorOp4_Law467 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law467 := by
  simp only [Law467.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 474 (2 variables). -/
theorem noXorOp4_Law474 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law474 := by
  simp only [Law474.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 481 (3 variables). -/
theorem noXorOp4_Law481 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law481 := by
  simp only [Law481.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 492 (3 variables). -/
theorem noXorOp4_Law492 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law492 := by
  simp only [Law492.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 504 (2 variables). -/
theorem noXorOp4_Law504 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law504 := by
  simp only [Law504.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 508 (3 variables). -/
theorem noXorOp4_Law508 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law508 := by
  simp only [Law508.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 543 (3 variables). -/
theorem noXorOp4_Law543 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law543 := by
  simp only [Law543.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 546 (3 variables). -/
theorem noXorOp4_Law546 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law546 := by
  simp only [Law546.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 667 (2 variables). -/
theorem noXorOp4_Law667 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law667 := by
  simp only [Law667.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 677 (2 variables). -/
theorem noXorOp4_Law677 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law677 := by
  simp only [Law677.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 695 (3 variables). -/
theorem noXorOp4_Law695 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law695 := by
  simp only [Law695.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 704 (2 variables). -/
theorem noXorOp4_Law704 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law704 := by
  simp only [Law704.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 870 (2 variables). -/
theorem noXorOp4_Law870 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law870 := by
  simp only [Law870.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 883 (2 variables). -/
theorem noXorOp4_Law883 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law883 := by
  simp only [Law883.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 895 (3 variables). -/
theorem noXorOp4_Law895 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law895 := by
  simp only [Law895.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 898 (3 variables). -/
theorem noXorOp4_Law898 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law898 := by
  simp only [Law898.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 907 (2 variables). -/
theorem noXorOp4_Law907 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law907 := by
  simp only [Law907.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 917 (2 variables). -/
theorem noXorOp4_Law917 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law917 := by
  simp only [Law917.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 978 (3 variables). -/
theorem noXorOp4_Law978 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law978 := by
  simp only [Law978.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1076 (2 variables). -/
theorem noXorOp4_Law1076 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1076 := by
  simp only [Law1076.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1083 (2 variables). -/
theorem noXorOp4_Law1083 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1083 := by
  simp only [Law1083.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1110 (2 variables). -/
theorem noXorOp4_Law1110 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1110 := by
  simp only [Law1110.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1279 (2 variables). -/
theorem noXorOp4_Law1279 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1279 := by
  simp only [Law1279.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1286 (2 variables). -/
theorem noXorOp4_Law1286 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1286 := by
  simp only [Law1286.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1313 (2 variables). -/
theorem noXorOp4_Law1313 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1313 := by
  simp only [Law1313.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1489 (2 variables). -/
theorem noXorOp4_Law1489 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1489 := by
  simp only [Law1489.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1516 (2 variables). -/
theorem noXorOp4_Law1516 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1516 := by
  simp only [Law1516.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1523 (3 variables). -/
theorem noXorOp4_Law1523 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1523 := by
  simp only [Law1523.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 1685 (2 variables). -/
theorem noXorOp4_Law1685 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law1685 := by
  simp only [Law1685.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3269 (2 variables). -/
theorem noXorOp4_Law3269 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3269 := by
  simp only [Law3269.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3279 (2 variables). -/
theorem noXorOp4_Law3279 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3279 := by
  simp only [Law3279.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3342 (2 variables). -/
theorem noXorOp4_Law3342 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3342 := by
  simp only [Law3342.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3345 (2 variables). -/
theorem noXorOp4_Law3345 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3345 := by
  simp only [Law3345.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3355 (2 variables). -/
theorem noXorOp4_Law3355 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3355 := by
  simp only [Law3355.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3364 (3 variables). -/
theorem noXorOp4_Law3364 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3364 := by
  simp only [Law3364.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3475 (2 variables). -/
theorem noXorOp4_Law3475 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3475 := by
  simp only [Law3475.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3482 (2 variables). -/
theorem noXorOp4_Law3482 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3482 := by
  simp only [Law3482.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3545 (2 variables). -/
theorem noXorOp4_Law3545 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3545 := by
  simp only [Law3545.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3548 (2 variables). -/
theorem noXorOp4_Law3548 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3548 := by
  simp only [Law3548.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3555 (2 variables). -/
theorem noXorOp4_Law3555 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3555 := by
  simp only [Law3555.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 3607 (3 variables). -/
theorem noXorOp4_Law3607 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law3607 := by
  simp only [Law3607.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4293 (2 variables). -/
theorem noXorOp4_Law4293 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4293 := by
  simp only [Law4293.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4321 (2 variables). -/
theorem noXorOp4_Law4321 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4321 := by
  simp only [Law4321.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4343 (2 variables). -/
theorem noXorOp4_Law4343 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4343 := by
  simp only [Law4343.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4364 (3 variables). -/
theorem noXorOp4_Law4364 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4364 := by
  simp only [Law4364.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4415 (3 variables). -/
theorem noXorOp4_Law4415 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4415 := by
  simp only [Law4415.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4443 (2 variables). -/
theorem noXorOp4_Law4443 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4443 := by
  simp only [Law4443.models_iff]
  native_decide

/-- No `x ↦ x ⊕ 1`-invariant operation on `Fin 4` satisfies equation 4541 (3 variables). -/
theorem noXorOp4_Law4541 : ∀ r₀ r₂ : Fin 4 → Fin 4,
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.xorOp4 r₀ r₂)) Law4541 := by
  simp only [Law4541.models_iff]
  native_decide

/-! ### The sources

A four-element model of each source admitting the symmetry. Several sources share a
model; the duplicates are kept apart so that each refutation names its own.
-/

/-- A model of equation 167 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM167 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![1, 3, 3, 0], ![2, 0, 1, 2], ![0, 3, 2, 0], ![2, 1, 1, 3]] x y

theorem xorM167_models : @satisfies _ (Fin 4) xorM167 Law167 :=
  (@Law167.models_iff (Fin 4) xorM167).mpr (by decide)

theorem xorM167_endo : xorM167.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 168 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM168 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![1, 2, 2, 1], ![3, 0, 0, 3], ![1, 2, 2, 1], ![3, 0, 0, 3]] x y

theorem xorM168_models : @satisfies _ (Fin 4) xorM168 Law168 :=
  (@Law168.models_iff (Fin 4) xorM168).mpr (by decide)

theorem xorM168_endo : xorM168.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 1480 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM1480 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 2, 0, 1], ![3, 1, 0, 1], ![3, 1, 3, 1], ![0, 2, 0, 2]] x y

theorem xorM1480_models : @satisfies _ (Fin 4) xorM1480 Law1480 :=
  (@Law1480.models_iff (Fin 4) xorM1480).mpr (by decide)

theorem xorM1480_endo : xorM1480.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 1483 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM1483 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![1, 2, 2, 1], ![3, 0, 0, 3], ![1, 2, 2, 1], ![3, 0, 0, 3]] x y

theorem xorM1483_models : @satisfies _ (Fin 4) xorM1483 Law1483 :=
  (@Law1483.models_iff (Fin 4) xorM1483).mpr (by decide)

theorem xorM1483_endo : xorM1483.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 1485 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM1485 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![1, 2, 2, 1], ![3, 0, 0, 3], ![1, 2, 2, 1], ![3, 0, 0, 3]] x y

theorem xorM1485_models : @satisfies _ (Fin 4) xorM1485 Law1485 :=
  (@Law1485.models_iff (Fin 4) xorM1485).mpr (by decide)

theorem xorM1485_endo : xorM1485.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 1486 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM1486 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![1, 2, 2, 1], ![3, 0, 0, 3], ![1, 2, 2, 1], ![3, 0, 0, 3]] x y

theorem xorM1486_models : @satisfies _ (Fin 4) xorM1486 Law1486 :=
  (@Law1486.models_iff (Fin 4) xorM1486).mpr (by decide)

theorem xorM1486_endo : xorM1486.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 1682 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM1682 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 2, 2, 1], ![3, 1, 0, 3], ![1, 2, 2, 1], ![3, 0, 0, 3]] x y

theorem xorM1682_models : @satisfies _ (Fin 4) xorM1682 Law1682 :=
  (@Law1682.models_iff (Fin 4) xorM1682).mpr (by decide)

theorem xorM1682_endo : xorM1682.IsEndo (Fin.xor4 1) := by decide

/-- A model of equation 3675 on `Fin 4` with `x ↦ x ⊕ 1` as an automorphism. -/
@[reducible]
def xorM3675 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 2, 2, 1], ![3, 1, 0, 3], ![1, 2, 2, 1], ![3, 0, 0, 3]] x y

theorem xorM3675_models : @satisfies _ (Fin 4) xorM3675 Law3675 :=
  (@Law3675.models_iff (Fin 4) xorM3675).mpr (by decide)

theorem xorM3675_endo : xorM3675.IsEndo (Fin.xor4 1) := by decide

/-! ### The refutations

301 cells over 8 sources and 54 targets. Each is the same
three facts assembled by `Law.MagmaLaw.not_definableFrom_xorOp4`; the carrier is
`Fin 4` throughout, so the finite-flavour refutations follow too.
-/

theorem Equation43_not_definableFrom_Equation167 :
    ¬ Law43.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law43

theorem Equation63_not_definableFrom_Equation167 :
    ¬ Law63.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law63

theorem Equation332_not_definableFrom_Equation167 :
    ¬ Law332.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation167 :
    ¬ Law464.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law464

theorem Equation504_not_definableFrom_Equation167 :
    ¬ Law504.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law504

theorem Equation546_not_definableFrom_Equation167 :
    ¬ Law546.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation167 :
    ¬ Law667.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law667

theorem Equation870_not_definableFrom_Equation167 :
    ¬ Law870.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation167 :
    ¬ Law883.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law883

theorem Equation917_not_definableFrom_Equation167 :
    ¬ Law917.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law917

theorem Equation1110_not_definableFrom_Equation167 :
    ¬ Law1110.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law1110

theorem Equation1685_not_definableFrom_Equation167 :
    ¬ Law1685.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law1685

theorem Equation3269_not_definableFrom_Equation167 :
    ¬ Law3269.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation167 :
    ¬ Law3279.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation167 :
    ¬ Law3342.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation167 :
    ¬ Law3345.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3345

theorem Equation3475_not_definableFrom_Equation167 :
    ¬ Law3475.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation167 :
    ¬ Law3482.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation167 :
    ¬ Law3545.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation167 :
    ¬ Law3548.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3548

theorem Equation3607_not_definableFrom_Equation167 :
    ¬ Law3607.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law3607

theorem Equation4321_not_definableFrom_Equation167 :
    ¬ Law4321.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation167 :
    ¬ Law4343.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law4343

theorem Equation4443_not_definableFrom_Equation167 :
    ¬ Law4443.DefinableFrom Law167 :=
  not_definableFrom_xorOp4 (xorM167 : Magma (Fin 4)) xorM167_models
    xorM167_endo noXorOp4_Law4443

theorem Equation2_not_definableFrom_Equation168 :
    ¬ Law2.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law2

theorem Equation40_not_definableFrom_Equation168 :
    ¬ Law40.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law40

theorem Equation43_not_definableFrom_Equation168 :
    ¬ Law43.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law43

theorem Equation63_not_definableFrom_Equation168 :
    ¬ Law63.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law63

theorem Equation332_not_definableFrom_Equation168 :
    ¬ Law332.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation168 :
    ¬ Law464.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law464

theorem Equation467_not_definableFrom_Equation168 :
    ¬ Law467.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law467

theorem Equation474_not_definableFrom_Equation168 :
    ¬ Law474.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law474

theorem Equation481_not_definableFrom_Equation168 :
    ¬ Law481.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law481

theorem Equation492_not_definableFrom_Equation168 :
    ¬ Law492.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law492

theorem Equation504_not_definableFrom_Equation168 :
    ¬ Law504.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law504

theorem Equation508_not_definableFrom_Equation168 :
    ¬ Law508.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law508

theorem Equation543_not_definableFrom_Equation168 :
    ¬ Law543.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law543

theorem Equation546_not_definableFrom_Equation168 :
    ¬ Law546.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation168 :
    ¬ Law667.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law667

theorem Equation677_not_definableFrom_Equation168 :
    ¬ Law677.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law677

theorem Equation695_not_definableFrom_Equation168 :
    ¬ Law695.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law695

theorem Equation704_not_definableFrom_Equation168 :
    ¬ Law704.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law704

theorem Equation870_not_definableFrom_Equation168 :
    ¬ Law870.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation168 :
    ¬ Law883.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law883

theorem Equation895_not_definableFrom_Equation168 :
    ¬ Law895.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law895

theorem Equation898_not_definableFrom_Equation168 :
    ¬ Law898.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law898

theorem Equation907_not_definableFrom_Equation168 :
    ¬ Law907.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law907

theorem Equation917_not_definableFrom_Equation168 :
    ¬ Law917.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law917

theorem Equation978_not_definableFrom_Equation168 :
    ¬ Law978.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law978

theorem Equation1076_not_definableFrom_Equation168 :
    ¬ Law1076.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1076

theorem Equation1083_not_definableFrom_Equation168 :
    ¬ Law1083.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1083

theorem Equation1110_not_definableFrom_Equation168 :
    ¬ Law1110.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1110

theorem Equation1279_not_definableFrom_Equation168 :
    ¬ Law1279.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1279

theorem Equation1286_not_definableFrom_Equation168 :
    ¬ Law1286.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1286

theorem Equation1313_not_definableFrom_Equation168 :
    ¬ Law1313.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1313

theorem Equation1489_not_definableFrom_Equation168 :
    ¬ Law1489.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1489

theorem Equation1516_not_definableFrom_Equation168 :
    ¬ Law1516.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1516

theorem Equation1523_not_definableFrom_Equation168 :
    ¬ Law1523.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1523

theorem Equation1685_not_definableFrom_Equation168 :
    ¬ Law1685.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law1685

theorem Equation3269_not_definableFrom_Equation168 :
    ¬ Law3269.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation168 :
    ¬ Law3279.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation168 :
    ¬ Law3342.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation168 :
    ¬ Law3345.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3345

theorem Equation3355_not_definableFrom_Equation168 :
    ¬ Law3355.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3355

theorem Equation3364_not_definableFrom_Equation168 :
    ¬ Law3364.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3364

theorem Equation3475_not_definableFrom_Equation168 :
    ¬ Law3475.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation168 :
    ¬ Law3482.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation168 :
    ¬ Law3545.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation168 :
    ¬ Law3548.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3548

theorem Equation3555_not_definableFrom_Equation168 :
    ¬ Law3555.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3555

theorem Equation3607_not_definableFrom_Equation168 :
    ¬ Law3607.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law3607

theorem Equation4293_not_definableFrom_Equation168 :
    ¬ Law4293.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4293

theorem Equation4321_not_definableFrom_Equation168 :
    ¬ Law4321.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation168 :
    ¬ Law4343.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4343

theorem Equation4364_not_definableFrom_Equation168 :
    ¬ Law4364.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4364

theorem Equation4415_not_definableFrom_Equation168 :
    ¬ Law4415.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4415

theorem Equation4443_not_definableFrom_Equation168 :
    ¬ Law4443.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4443

theorem Equation4541_not_definableFrom_Equation168 :
    ¬ Law4541.DefinableFrom Law168 :=
  not_definableFrom_xorOp4 (xorM168 : Magma (Fin 4)) xorM168_models
    xorM168_endo noXorOp4_Law4541

theorem Equation2_not_definableFrom_Equation1480 :
    ¬ Law2.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law2

theorem Equation40_not_definableFrom_Equation1480 :
    ¬ Law40.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law40

theorem Equation43_not_definableFrom_Equation1480 :
    ¬ Law43.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law43

theorem Equation63_not_definableFrom_Equation1480 :
    ¬ Law63.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law63

theorem Equation332_not_definableFrom_Equation1480 :
    ¬ Law332.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation1480 :
    ¬ Law464.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law464

theorem Equation467_not_definableFrom_Equation1480 :
    ¬ Law467.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law467

theorem Equation474_not_definableFrom_Equation1480 :
    ¬ Law474.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law474

theorem Equation481_not_definableFrom_Equation1480 :
    ¬ Law481.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law481

theorem Equation492_not_definableFrom_Equation1480 :
    ¬ Law492.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law492

theorem Equation504_not_definableFrom_Equation1480 :
    ¬ Law504.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law504

theorem Equation508_not_definableFrom_Equation1480 :
    ¬ Law508.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law508

theorem Equation543_not_definableFrom_Equation1480 :
    ¬ Law543.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law543

theorem Equation546_not_definableFrom_Equation1480 :
    ¬ Law546.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation1480 :
    ¬ Law667.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law667

theorem Equation677_not_definableFrom_Equation1480 :
    ¬ Law677.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law677

theorem Equation695_not_definableFrom_Equation1480 :
    ¬ Law695.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law695

theorem Equation704_not_definableFrom_Equation1480 :
    ¬ Law704.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law704

theorem Equation870_not_definableFrom_Equation1480 :
    ¬ Law870.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation1480 :
    ¬ Law883.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law883

theorem Equation895_not_definableFrom_Equation1480 :
    ¬ Law895.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law895

theorem Equation898_not_definableFrom_Equation1480 :
    ¬ Law898.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law898

theorem Equation907_not_definableFrom_Equation1480 :
    ¬ Law907.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law907

theorem Equation917_not_definableFrom_Equation1480 :
    ¬ Law917.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law917

theorem Equation978_not_definableFrom_Equation1480 :
    ¬ Law978.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law978

theorem Equation1076_not_definableFrom_Equation1480 :
    ¬ Law1076.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1076

theorem Equation1083_not_definableFrom_Equation1480 :
    ¬ Law1083.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1083

theorem Equation1110_not_definableFrom_Equation1480 :
    ¬ Law1110.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1110

theorem Equation1279_not_definableFrom_Equation1480 :
    ¬ Law1279.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1279

theorem Equation1286_not_definableFrom_Equation1480 :
    ¬ Law1286.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1286

theorem Equation1313_not_definableFrom_Equation1480 :
    ¬ Law1313.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1313

theorem Equation1489_not_definableFrom_Equation1480 :
    ¬ Law1489.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1489

theorem Equation1516_not_definableFrom_Equation1480 :
    ¬ Law1516.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1516

theorem Equation1523_not_definableFrom_Equation1480 :
    ¬ Law1523.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1523

theorem Equation1685_not_definableFrom_Equation1480 :
    ¬ Law1685.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law1685

theorem Equation3269_not_definableFrom_Equation1480 :
    ¬ Law3269.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation1480 :
    ¬ Law3279.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation1480 :
    ¬ Law3342.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation1480 :
    ¬ Law3345.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3345

theorem Equation3355_not_definableFrom_Equation1480 :
    ¬ Law3355.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3355

theorem Equation3364_not_definableFrom_Equation1480 :
    ¬ Law3364.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3364

theorem Equation3475_not_definableFrom_Equation1480 :
    ¬ Law3475.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation1480 :
    ¬ Law3482.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation1480 :
    ¬ Law3545.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation1480 :
    ¬ Law3548.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3548

theorem Equation3555_not_definableFrom_Equation1480 :
    ¬ Law3555.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3555

theorem Equation3607_not_definableFrom_Equation1480 :
    ¬ Law3607.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law3607

theorem Equation4293_not_definableFrom_Equation1480 :
    ¬ Law4293.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4293

theorem Equation4321_not_definableFrom_Equation1480 :
    ¬ Law4321.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation1480 :
    ¬ Law4343.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4343

theorem Equation4364_not_definableFrom_Equation1480 :
    ¬ Law4364.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4364

theorem Equation4415_not_definableFrom_Equation1480 :
    ¬ Law4415.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4415

theorem Equation4443_not_definableFrom_Equation1480 :
    ¬ Law4443.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4443

theorem Equation4541_not_definableFrom_Equation1480 :
    ¬ Law4541.DefinableFrom Law1480 :=
  not_definableFrom_xorOp4 (xorM1480 : Magma (Fin 4)) xorM1480_models
    xorM1480_endo noXorOp4_Law4541

theorem Equation40_not_definableFrom_Equation1483 :
    ¬ Law40.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law40

theorem Equation43_not_definableFrom_Equation1483 :
    ¬ Law43.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law43

theorem Equation332_not_definableFrom_Equation1483 :
    ¬ Law332.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation1483 :
    ¬ Law464.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law464

theorem Equation481_not_definableFrom_Equation1483 :
    ¬ Law481.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law481

theorem Equation492_not_definableFrom_Equation1483 :
    ¬ Law492.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law492

theorem Equation504_not_definableFrom_Equation1483 :
    ¬ Law504.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law504

theorem Equation508_not_definableFrom_Equation1483 :
    ¬ Law508.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law508

theorem Equation543_not_definableFrom_Equation1483 :
    ¬ Law543.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law543

theorem Equation546_not_definableFrom_Equation1483 :
    ¬ Law546.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation1483 :
    ¬ Law667.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law667

theorem Equation695_not_definableFrom_Equation1483 :
    ¬ Law695.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law695

theorem Equation870_not_definableFrom_Equation1483 :
    ¬ Law870.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation1483 :
    ¬ Law883.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law883

theorem Equation895_not_definableFrom_Equation1483 :
    ¬ Law895.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law895

theorem Equation898_not_definableFrom_Equation1483 :
    ¬ Law898.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law898

theorem Equation917_not_definableFrom_Equation1483 :
    ¬ Law917.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law917

theorem Equation978_not_definableFrom_Equation1483 :
    ¬ Law978.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law978

theorem Equation1523_not_definableFrom_Equation1483 :
    ¬ Law1523.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law1523

theorem Equation3269_not_definableFrom_Equation1483 :
    ¬ Law3269.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation1483 :
    ¬ Law3279.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation1483 :
    ¬ Law3342.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation1483 :
    ¬ Law3345.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3345

theorem Equation3355_not_definableFrom_Equation1483 :
    ¬ Law3355.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3355

theorem Equation3364_not_definableFrom_Equation1483 :
    ¬ Law3364.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3364

theorem Equation3475_not_definableFrom_Equation1483 :
    ¬ Law3475.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation1483 :
    ¬ Law3482.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation1483 :
    ¬ Law3545.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation1483 :
    ¬ Law3548.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3548

theorem Equation3555_not_definableFrom_Equation1483 :
    ¬ Law3555.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3555

theorem Equation3607_not_definableFrom_Equation1483 :
    ¬ Law3607.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law3607

theorem Equation4293_not_definableFrom_Equation1483 :
    ¬ Law4293.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4293

theorem Equation4321_not_definableFrom_Equation1483 :
    ¬ Law4321.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation1483 :
    ¬ Law4343.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4343

theorem Equation4364_not_definableFrom_Equation1483 :
    ¬ Law4364.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4364

theorem Equation4415_not_definableFrom_Equation1483 :
    ¬ Law4415.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4415

theorem Equation4443_not_definableFrom_Equation1483 :
    ¬ Law4443.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4443

theorem Equation4541_not_definableFrom_Equation1483 :
    ¬ Law4541.DefinableFrom Law1483 :=
  not_definableFrom_xorOp4 (xorM1483 : Magma (Fin 4)) xorM1483_models
    xorM1483_endo noXorOp4_Law4541

theorem Equation40_not_definableFrom_Equation1485 :
    ¬ Law40.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law40

theorem Equation43_not_definableFrom_Equation1485 :
    ¬ Law43.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law43

theorem Equation332_not_definableFrom_Equation1485 :
    ¬ Law332.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation1485 :
    ¬ Law464.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law464

theorem Equation481_not_definableFrom_Equation1485 :
    ¬ Law481.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law481

theorem Equation492_not_definableFrom_Equation1485 :
    ¬ Law492.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law492

theorem Equation504_not_definableFrom_Equation1485 :
    ¬ Law504.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law504

theorem Equation508_not_definableFrom_Equation1485 :
    ¬ Law508.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law508

theorem Equation543_not_definableFrom_Equation1485 :
    ¬ Law543.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law543

theorem Equation546_not_definableFrom_Equation1485 :
    ¬ Law546.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation1485 :
    ¬ Law667.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law667

theorem Equation695_not_definableFrom_Equation1485 :
    ¬ Law695.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law695

theorem Equation870_not_definableFrom_Equation1485 :
    ¬ Law870.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation1485 :
    ¬ Law883.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law883

theorem Equation895_not_definableFrom_Equation1485 :
    ¬ Law895.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law895

theorem Equation898_not_definableFrom_Equation1485 :
    ¬ Law898.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law898

theorem Equation917_not_definableFrom_Equation1485 :
    ¬ Law917.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law917

theorem Equation978_not_definableFrom_Equation1485 :
    ¬ Law978.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law978

theorem Equation1523_not_definableFrom_Equation1485 :
    ¬ Law1523.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law1523

theorem Equation3269_not_definableFrom_Equation1485 :
    ¬ Law3269.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation1485 :
    ¬ Law3279.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation1485 :
    ¬ Law3342.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation1485 :
    ¬ Law3345.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3345

theorem Equation3355_not_definableFrom_Equation1485 :
    ¬ Law3355.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3355

theorem Equation3364_not_definableFrom_Equation1485 :
    ¬ Law3364.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3364

theorem Equation3475_not_definableFrom_Equation1485 :
    ¬ Law3475.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation1485 :
    ¬ Law3482.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation1485 :
    ¬ Law3545.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation1485 :
    ¬ Law3548.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3548

theorem Equation3555_not_definableFrom_Equation1485 :
    ¬ Law3555.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3555

theorem Equation3607_not_definableFrom_Equation1485 :
    ¬ Law3607.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law3607

theorem Equation4293_not_definableFrom_Equation1485 :
    ¬ Law4293.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4293

theorem Equation4321_not_definableFrom_Equation1485 :
    ¬ Law4321.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation1485 :
    ¬ Law4343.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4343

theorem Equation4364_not_definableFrom_Equation1485 :
    ¬ Law4364.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4364

theorem Equation4415_not_definableFrom_Equation1485 :
    ¬ Law4415.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4415

theorem Equation4443_not_definableFrom_Equation1485 :
    ¬ Law4443.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4443

theorem Equation4541_not_definableFrom_Equation1485 :
    ¬ Law4541.DefinableFrom Law1485 :=
  not_definableFrom_xorOp4 (xorM1485 : Magma (Fin 4)) xorM1485_models
    xorM1485_endo noXorOp4_Law4541

theorem Equation2_not_definableFrom_Equation1486 :
    ¬ Law2.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law2

theorem Equation40_not_definableFrom_Equation1486 :
    ¬ Law40.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law40

theorem Equation43_not_definableFrom_Equation1486 :
    ¬ Law43.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law43

theorem Equation63_not_definableFrom_Equation1486 :
    ¬ Law63.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law63

theorem Equation332_not_definableFrom_Equation1486 :
    ¬ Law332.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation1486 :
    ¬ Law464.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law464

theorem Equation467_not_definableFrom_Equation1486 :
    ¬ Law467.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law467

theorem Equation474_not_definableFrom_Equation1486 :
    ¬ Law474.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law474

theorem Equation481_not_definableFrom_Equation1486 :
    ¬ Law481.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law481

theorem Equation492_not_definableFrom_Equation1486 :
    ¬ Law492.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law492

theorem Equation504_not_definableFrom_Equation1486 :
    ¬ Law504.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law504

theorem Equation508_not_definableFrom_Equation1486 :
    ¬ Law508.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law508

theorem Equation543_not_definableFrom_Equation1486 :
    ¬ Law543.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law543

theorem Equation546_not_definableFrom_Equation1486 :
    ¬ Law546.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation1486 :
    ¬ Law667.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law667

theorem Equation677_not_definableFrom_Equation1486 :
    ¬ Law677.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law677

theorem Equation695_not_definableFrom_Equation1486 :
    ¬ Law695.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law695

theorem Equation704_not_definableFrom_Equation1486 :
    ¬ Law704.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law704

theorem Equation870_not_definableFrom_Equation1486 :
    ¬ Law870.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation1486 :
    ¬ Law883.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law883

theorem Equation895_not_definableFrom_Equation1486 :
    ¬ Law895.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law895

theorem Equation898_not_definableFrom_Equation1486 :
    ¬ Law898.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law898

theorem Equation907_not_definableFrom_Equation1486 :
    ¬ Law907.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law907

theorem Equation917_not_definableFrom_Equation1486 :
    ¬ Law917.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law917

theorem Equation978_not_definableFrom_Equation1486 :
    ¬ Law978.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law978

theorem Equation1076_not_definableFrom_Equation1486 :
    ¬ Law1076.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1076

theorem Equation1083_not_definableFrom_Equation1486 :
    ¬ Law1083.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1083

theorem Equation1110_not_definableFrom_Equation1486 :
    ¬ Law1110.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1110

theorem Equation1279_not_definableFrom_Equation1486 :
    ¬ Law1279.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1279

theorem Equation1286_not_definableFrom_Equation1486 :
    ¬ Law1286.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1286

theorem Equation1313_not_definableFrom_Equation1486 :
    ¬ Law1313.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1313

theorem Equation1489_not_definableFrom_Equation1486 :
    ¬ Law1489.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1489

theorem Equation1516_not_definableFrom_Equation1486 :
    ¬ Law1516.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1516

theorem Equation1523_not_definableFrom_Equation1486 :
    ¬ Law1523.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1523

theorem Equation1685_not_definableFrom_Equation1486 :
    ¬ Law1685.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law1685

theorem Equation3269_not_definableFrom_Equation1486 :
    ¬ Law3269.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation1486 :
    ¬ Law3279.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation1486 :
    ¬ Law3342.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation1486 :
    ¬ Law3345.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3345

theorem Equation3355_not_definableFrom_Equation1486 :
    ¬ Law3355.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3355

theorem Equation3364_not_definableFrom_Equation1486 :
    ¬ Law3364.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3364

theorem Equation3475_not_definableFrom_Equation1486 :
    ¬ Law3475.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation1486 :
    ¬ Law3482.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation1486 :
    ¬ Law3545.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation1486 :
    ¬ Law3548.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3548

theorem Equation3555_not_definableFrom_Equation1486 :
    ¬ Law3555.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3555

theorem Equation3607_not_definableFrom_Equation1486 :
    ¬ Law3607.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law3607

theorem Equation4293_not_definableFrom_Equation1486 :
    ¬ Law4293.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4293

theorem Equation4321_not_definableFrom_Equation1486 :
    ¬ Law4321.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation1486 :
    ¬ Law4343.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4343

theorem Equation4364_not_definableFrom_Equation1486 :
    ¬ Law4364.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4364

theorem Equation4415_not_definableFrom_Equation1486 :
    ¬ Law4415.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4415

theorem Equation4443_not_definableFrom_Equation1486 :
    ¬ Law4443.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4443

theorem Equation4541_not_definableFrom_Equation1486 :
    ¬ Law4541.DefinableFrom Law1486 :=
  not_definableFrom_xorOp4 (xorM1486 : Magma (Fin 4)) xorM1486_models
    xorM1486_endo noXorOp4_Law4541

theorem Equation43_not_definableFrom_Equation1682 :
    ¬ Law43.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law43

theorem Equation332_not_definableFrom_Equation1682 :
    ¬ Law332.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation1682 :
    ¬ Law464.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law464

theorem Equation504_not_definableFrom_Equation1682 :
    ¬ Law504.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law504

theorem Equation546_not_definableFrom_Equation1682 :
    ¬ Law546.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law546

theorem Equation667_not_definableFrom_Equation1682 :
    ¬ Law667.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law667

theorem Equation870_not_definableFrom_Equation1682 :
    ¬ Law870.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law870

theorem Equation883_not_definableFrom_Equation1682 :
    ¬ Law883.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law883

theorem Equation917_not_definableFrom_Equation1682 :
    ¬ Law917.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law917

theorem Equation3269_not_definableFrom_Equation1682 :
    ¬ Law3269.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation1682 :
    ¬ Law3279.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation1682 :
    ¬ Law3342.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation1682 :
    ¬ Law3345.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3345

theorem Equation3475_not_definableFrom_Equation1682 :
    ¬ Law3475.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation1682 :
    ¬ Law3482.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation1682 :
    ¬ Law3545.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation1682 :
    ¬ Law3548.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3548

theorem Equation3607_not_definableFrom_Equation1682 :
    ¬ Law3607.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law3607

theorem Equation4321_not_definableFrom_Equation1682 :
    ¬ Law4321.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation1682 :
    ¬ Law4343.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law4343

theorem Equation4443_not_definableFrom_Equation1682 :
    ¬ Law4443.DefinableFrom Law1682 :=
  not_definableFrom_xorOp4 (xorM1682 : Magma (Fin 4)) xorM1682_models
    xorM1682_endo noXorOp4_Law4443

theorem Equation43_not_definableFrom_Equation3675 :
    ¬ Law43.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law43

theorem Equation332_not_definableFrom_Equation3675 :
    ¬ Law332.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law332

theorem Equation464_not_definableFrom_Equation3675 :
    ¬ Law464.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law464

theorem Equation504_not_definableFrom_Equation3675 :
    ¬ Law504.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law504

theorem Equation870_not_definableFrom_Equation3675 :
    ¬ Law870.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law870

theorem Equation917_not_definableFrom_Equation3675 :
    ¬ Law917.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law917

theorem Equation3269_not_definableFrom_Equation3675 :
    ¬ Law3269.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3269

theorem Equation3279_not_definableFrom_Equation3675 :
    ¬ Law3279.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3279

theorem Equation3342_not_definableFrom_Equation3675 :
    ¬ Law3342.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3342

theorem Equation3345_not_definableFrom_Equation3675 :
    ¬ Law3345.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3345

theorem Equation3475_not_definableFrom_Equation3675 :
    ¬ Law3475.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3475

theorem Equation3482_not_definableFrom_Equation3675 :
    ¬ Law3482.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3482

theorem Equation3545_not_definableFrom_Equation3675 :
    ¬ Law3545.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3545

theorem Equation3548_not_definableFrom_Equation3675 :
    ¬ Law3548.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3548

theorem Equation3607_not_definableFrom_Equation3675 :
    ¬ Law3607.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law3607

theorem Equation4321_not_definableFrom_Equation3675 :
    ¬ Law4321.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law4321

theorem Equation4343_not_definableFrom_Equation3675 :
    ¬ Law4343.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law4343

theorem Equation4443_not_definableFrom_Equation3675 :
    ¬ Law4443.DefinableFrom Law3675 :=
  not_definableFrom_xorOp4 (xorM3675 : Magma (Fin 4)) xorM3675_models
    xorM3675_endo noXorOp4_Law4443
