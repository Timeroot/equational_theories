import equational_theories.Definability.Negative
import equational_theories.Equations.All
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The rationals under `min`, and the four operations definable on them

`Definability/Semilattice.lean` refutes `4364 → 40` and `4541 → 40` over all magmas with the free
semilattice and one fixed-point-free automorphism. That certificate is deliberately weak: it uses a
single symmetry, so it can only reach targets that force a canonical element. The same two sources
support a much stronger certificate, and this file builds it.

Take the rationals under `min`. Every law whose two sides have the same variables holds there,
because a term evaluates to the minimum of its variables; `4364` and `4541` are two such laws. What
makes `ℚ` the right carrier is the automorphism group: every order-preserving map is an
automorphism of `min`, and already the *affine* ones `t ↦ a t + b` with `a > 0` are enough to pin
an invariant operation down to two rational parameters,

    f x y = x + c (y - x)  for x < y,    f x y = y + d (x - y)  for y < x,    f x x = x,

with `c = f 0 1` and `d = f 1 0`, because the affine group is sharply transitive on ordered pairs.
One non-affine automorphism then finishes the job: `kink` below is a piecewise-affine
order-automorphism of `ℚ` whose fixed points are exactly `0` and `1`, so `c` and `d` are each `0`
or `1`, and the four resulting operations are `min`, `max`, and the two projections. A target
satisfied by none of those four is refuted, over all magmas.

Nothing here works over a finite carrier: a finite linear order has no automorphisms at all. The
finite flavour of these cells is *positive* -- see `Definability/IdemBottom.lean`.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The rationals under `min`: a semilattice with a large automorphism group. -/
@[implicit_reducible]
def minMagma : Magma ℚ := ⟨fun x y ↦ min x y⟩

@[simp]
theorem minMagma_op (x y : ℚ) : minMagma.op x y = min x y := rfl

/-- Every monotone permutation of `ℚ` is an automorphism of `min`. -/
theorem minMagma_isEndo {e : ℚ ≃ ℚ} (he : Monotone ⇑e) : minMagma.IsEndo ⇑e :=
  fun _ _ ↦ he.map_min

theorem minMagma_4364 : @Equation4364 ℚ minMagma := fun x y z ↦ by
  simp only [minMagma_op]
  rcases le_total x y with h₁ | h₁ <;> rcases le_total y z with h₂ | h₂ <;>
    rcases le_total x z with h₃ | h₃ <;> simp_all <;> linarith

theorem minMagma_4541 : @Equation4541 ℚ minMagma := fun x y z ↦ by
  simp only [minMagma_op]
  rcases le_total x y with h₁ | h₁ <;> rcases le_total y z with h₂ | h₂ <;>
    rcases le_total x z with h₃ | h₃ <;> simp_all <;> linarith

/-! ### The affine automorphisms -/

/-- `t ↦ a t + b` with `a > 0`, as a permutation of `ℚ`. -/
def affEquiv (a b : ℚ) (ha : a ≠ 0) : ℚ ≃ ℚ where
  toFun t := a * t + b
  invFun u := (u - b) / a
  left_inv t := by field_simp; ring
  right_inv u := by field_simp; ring

@[simp]
theorem affEquiv_apply (a b : ℚ) (ha : a ≠ 0) (t : ℚ) : affEquiv a b ha t = a * t + b := rfl

theorem affEquiv_monotone {a b : ℚ} (ha : 0 < a) : Monotone ⇑(affEquiv a b ha.ne') :=
  fun _ _ h ↦ by simp only [affEquiv_apply]; nlinarith

/-! ### One non-affine automorphism, with fixed points exactly `0` and `1` -/

/-- A four-piece increasing piecewise-affine bijection of `ℚ`, fixing `0` and `1` and nothing
else: it doubles below `0`, halves on `[0, 1/2]`, has slope `3/2` on `[1/2, 1]` and doubles
again above `1`. -/
def kink (t : ℚ) : ℚ :=
  if t ≤ 0 then 2 * t
  else if t ≤ 1 / 2 then t / 2
  else if t ≤ 1 then (3 * t - 1) / 2
  else 2 * t - 1

/-- The inverse of `kink`, with breakpoints at the images `0`, `1/4`, `1`. -/
def kinkInv (u : ℚ) : ℚ :=
  if u ≤ 0 then u / 2
  else if u ≤ 1 / 4 then 2 * u
  else if u ≤ 1 then (2 * u + 1) / 3
  else (u + 1) / 2

theorem kink_monotone : Monotone kink := by
  intro s t h
  unfold kink
  split_ifs <;> linarith

/-- `kink` as a permutation of `ℚ`. -/
def kinkEquiv : ℚ ≃ ℚ where
  toFun := kink
  invFun := kinkInv
  left_inv t := by unfold kink kinkInv; split_ifs <;> linarith
  right_inv u := by unfold kink kinkInv; split_ifs <;> linarith

@[simp] theorem kinkEquiv_apply (t : ℚ) : kinkEquiv t = kink t := rfl

@[simp] theorem kink_zero : kink 0 = 0 := by norm_num [kink]

@[simp] theorem kink_one : kink 1 = 1 := by norm_num [kink]

theorem kink_monotone' : Monotone ⇑kinkEquiv := kink_monotone

/-- The only rationals `kink` fixes are `0` and `1`. -/
theorem eq_zero_or_one_of_kink_eq {t : ℚ} (h : kink t = t) : t = 0 ∨ t = 1 := by
  unfold kink at h
  split_ifs at h
  · left; linarith
  · left; linarith
  · right; linarith
  · right; linarith

/-! ### What an invariant operation on `(ℚ, min)` can be -/

variable {M' : Magma ℚ} (h : ∀ e : ℚ ≃ ℚ, Monotone ⇑e → M'.IsEndo ⇑e)

include h

theorem op_diag (x : ℚ) : M'.op x x = x := by
  have hx : (2 : ℚ) * x + -x = x := by ring
  have := h (affEquiv 2 (-x) two_ne_zero) (affEquiv_monotone two_pos) x x
  simp only [affEquiv_apply, hx] at this
  linarith

theorem op_of_lt {x y : ℚ} (hxy : x < y) : M'.op x y = x + M'.op 0 1 * (y - x) := by
  have hpos : (0 : ℚ) < y - x := sub_pos.mpr hxy
  have h0 : (y - x) * (0 : ℚ) + x = x := by ring
  have h1 : (y - x) * (1 : ℚ) + x = y := by ring
  have := h (affEquiv (y - x) x hpos.ne') (affEquiv_monotone hpos) 0 1
  simp only [affEquiv_apply, h0, h1] at this
  linarith [this]

theorem op_of_gt {x y : ℚ} (hxy : y < x) : M'.op x y = y + M'.op 1 0 * (x - y) := by
  have hpos : (0 : ℚ) < x - y := sub_pos.mpr hxy
  have h0 : (x - y) * (0 : ℚ) + y = y := by ring
  have h1 : (x - y) * (1 : ℚ) + y = x := by ring
  have := h (affEquiv (x - y) y hpos.ne') (affEquiv_monotone hpos) 1 0
  simp only [affEquiv_apply, h0, h1] at this
  linarith [this]

theorem op_zero_one : M'.op 0 1 = 0 ∨ M'.op 0 1 = 1 := by
  have := h kinkEquiv kink_monotone' 0 1
  simp only [kinkEquiv_apply, kink_zero, kink_one] at this
  exact eq_zero_or_one_of_kink_eq this

theorem op_one_zero : M'.op 1 0 = 0 ∨ M'.op 1 0 = 1 := by
  have := h kinkEquiv kink_monotone' 1 0
  simp only [kinkEquiv_apply, kink_zero, kink_one] at this
  exact eq_zero_or_one_of_kink_eq this

/-- An operation invariant under all monotone permutations of `ℚ` is `min`, `max`, or one of the
two projections. -/
theorem op_cases :
    (∀ x y : ℚ, M'.op x y = min x y) ∨ (∀ x y : ℚ, M'.op x y = max x y) ∨
      (∀ x y : ℚ, M'.op x y = x) ∨ (∀ x y : ℚ, M'.op x y = y) := by
  have key : ∀ x y : ℚ, x < y → M'.op x y = x + M'.op 0 1 * (y - x) := fun _ _ ↦ op_of_lt h
  have key' : ∀ x y : ℚ, y < x → M'.op x y = y + M'.op 1 0 * (x - y) := fun _ _ ↦ op_of_gt h
  rcases op_zero_one h with hc | hc <;> rcases op_one_zero h with hd | hd
  · left
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · rw [key x y hxy, hc, min_eq_left hxy.le]; ring
    · rw [op_diag h, min_self]
    · rw [key' x y hxy, hd, min_eq_right hxy.le]; ring
  · right; right; left
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · rw [key x y hxy, hc]; ring
    · exact op_diag h _
    · rw [key' x y hxy, hd]; ring
  · right; right; right
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · rw [key x y hxy, hc]; ring
    · exact op_diag h _
    · rw [key' x y hxy, hd]; ring
  · right; left
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · rw [key x y hxy, hc, max_eq_right hxy.le]; ring
    · rw [op_diag h, max_self]
    · rw [key' x y hxy, hd, max_eq_left hxy.le]; ring

end Magma

open Magma

/-- The certificate. If a law fails in all four of `min`, `max` and the two projections on `ℚ`,
it is not definable from any law that `min` satisfies. -/
theorem not_definableFrom_minMagma {β : Type*} {L L' : Law.MagmaLaw β}
    (hM : @satisfies _ ℚ minMagma L')
    (h1 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ L)
    (h2 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ L)
    (h3 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ L)
    (h4 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ L) : ¬ L.DefinableFrom L' := by
  refine not_definableFrom_of_autos minMagma hM ?_
  rintro ⟨op⟩ hM' hle
  have h : ∀ e : ℚ ≃ ℚ, Monotone ⇑e → (Magma.mk op).IsEndo ⇑e :=
    fun e he ↦ hle (minMagma_isEndo he)
  rcases op_cases h with hop | hop | hop | hop
  · exact h1 (by convert hM' using 2; exact (funext fun x ↦ funext fun y ↦ hop x y).symm)
  · exact h2 (by convert hM' using 2; exact (funext fun x ↦ funext fun y ↦ hop x y).symm)
  · exact h3 (by convert hM' using 2; exact (funext fun x ↦ funext fun y ↦ hop x y).symm)
  · exact h4 (by convert hM' using 2; exact (funext fun x ↦ funext fun y ↦ hop x y).symm)
