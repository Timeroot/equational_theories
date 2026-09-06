import Mathlib.Tactic.Ring
import equational_theories.DecideBang
import Mathlib.Tactic.LinearCombination
import equational_theories.Definability.F16
import equational_theories.Definability.Negative
import equational_theories.Equations.All

/-!
# The homogeneous obstruction on `F₁₆`, and the two cells it closes

Law `1516`, `x = (y ◇ y) ◇ (x ◇ (x ◇ y))`, has the linear model `x ◇ y = a x + b y` on `F₁₆`, where
`b` is a root of `X⁴ + X + 1` and `a = (b + b²)⁻¹`. Every nonzero scalar is an automorphism of that
model, so every operation definable from it is *homogeneous*:

    W (a x) (a y) = a * W x y   for every `a ≠ 0`.

This file shows that **no** homogeneous operation on `F₁₆` satisfies law `467`,
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`, and hence that `467` is not definable from `1516`. The
opposite-magma mirror gives `3140` from `2091` at the same time.

The family here has `16¹⁷` members, so it cannot be enumerated the way
`Definability/AutTransport.lean` enumerates its symmetry families; the obstruction is discharged by
algebra instead. Homogeneity makes `W` a function of one variable: writing `L v = W 1 v`, we have
`W x y = x * L (y / x)` for `x ≠ 0` and `W 0 y = y * g` with `g = W 0 1`, and law `467` becomes

    (A)  L (x * L (L (c / x))) = x     for `x ≠ 0`, where `c = L 1`;
    (B)  L s * g = 1                   where `s = L 0`;
    (C)  L (c g²) = 0.

`L` is onto by (A) and (C), hence a permutation. Multiplying (A) over the fourteen `x ∉ {0, s}` and
reindexing both sides — the two products run over complements of pairs, and the products of *all*
nonzero elements agree — pins the one relation the pointwise consequences miss,

    (D)  s = c g³,

and without it the argument really does stall: `460` of the `3375` triples `(c, g, s)` survive
every pointwise consequence. With (D) in hand, nine values of `L` and three of `L²` are forced,

    L 0 = c g³    L 1 = c        L c = c⁻¹      L (c g) = g⁻²    L (c g²) = 0
    L (c g³) = g⁻¹        L (c g⁴) = (c g⁵)⁻¹   L (g⁻²) = c g⁴   L (g⁻³) = c g²
    L² 1 = c⁻¹    L² (c² g⁵) = c² g⁹            L² (g⁻⁴) = (c g⁶)⁻¹

and for no pair `(c, g)` of nonzero elements is that a partial injection — a `decide` over the
`225` pairs. The step that fails is field-specific: it needs `g⁻⁶ = g⁹`, i.e. `|F*| = 15`. Over
`F₅`, `F₇`, `F₈` and `F₉` homogeneous companions for `467` genuinely exist, so no smaller field
would do.
-/

open Law Law.MagmaLaw Finset

namespace Hom467

/-- A binary operation on `F₁₆` is *homogeneous* when every nonzero scalar is an automorphism of
it. This is exactly the invariance that first-order definability from the linear model of `1516`
guarantees. -/
def Homog (W : F16 → F16 → F16) : Prop := ∀ a x y : F16, a ≠ 0 → W (a * x) (a * y) = a * W x y

private theorem solve {a b d : F16} (ha : a ≠ 0) (h : a * b = d) : b = a⁻¹ * d := by
  rw [← h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-! ### Reindexing a product over the complement of a pair -/

/-- If `f` is injective off `{a, b}` and misses `u` and `v` there, it carries the complement of
`{a, b}` onto the complement of `{u, v}` — both have fourteen elements — so the two products
agree. -/
theorem prod_reindex {f : F16 → F16} {a b u v : F16} (hab : a ≠ b) (huv : u ≠ v)
    (hf : ∀ x ∈ univ \ ({a, b} : Finset F16), ∀ y ∈ univ \ ({a, b} : Finset F16),
      f x = f y → x = y)
    (hu : ∀ x ∈ univ \ ({a, b} : Finset F16), f x ≠ u)
    (hv : ∀ x ∈ univ \ ({a, b} : Finset F16), f x ≠ v) :
    ∏ x ∈ univ \ ({a, b} : Finset F16), f x = ∏ y ∈ univ \ ({u, v} : Finset F16), y := by
  have hcard : ∀ p q : F16, p ≠ q → (univ \ ({p, q} : Finset F16)).card = 14 := by
    intro p q hpq
    rw [Finset.card_univ_diff, Finset.card_insert_of_notMem (by simpa),
      Finset.card_singleton]
    rfl
  have himg : (univ \ ({a, b} : Finset F16)).image f = univ \ ({u, v} : Finset F16) := by
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨hu x hx, hv x hx⟩
    · rw [Finset.card_image_of_injOn hf, hcard a b hab, hcard u v huv]
  rw [← himg, Finset.prod_image hf]

/-! ### The twelve forced values, and why they cannot all hold -/

/-- Two of the listed pairs contradict injectivity: either they share an argument and differ in
value, or they differ in argument and share a value. -/
def Collide (l : List (F16 × F16)) : Prop :=
  ∃ p ∈ l, ∃ q ∈ l, (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.1 ≠ q.1 ∧ p.2 = q.2)

instance (l : List (F16 × F16)) : Decidable (Collide l) := by unfold Collide; infer_instance

/-- The nine values of `L` that law `467` forces, as a function of `c` and `g`. -/
def pinsL (c g : F16) : List (F16 × F16) :=
  [(0, c * (g * g * g)), (1, c), (c, c⁻¹), (c * g, (g * g)⁻¹), (c * (g * g), 0),
   (c * (g * g * g), g⁻¹), (c * (g * g * g * g), (c * (g * g * g * g * g))⁻¹),
   ((g * g)⁻¹, c * (g * g * g * g)), ((g * g * g)⁻¹, c * (g * g))]

/-- The three values of `L²` that law `467` forces beyond those. -/
def pinsL2 (c g : F16) : List (F16 × F16) :=
  [(1, c⁻¹),
   (c * c * (g * g * g * g * g), c * c * (g * g * g * g * g * g * g * g * g)),
   ((g * g * g * g)⁻¹, (c * (g * g * g * g * g * g))⁻¹)]

/-- **The finite check.** For no pair of nonzero elements are the twelve forced values consistent
with `L` and `L²` being injective. This is where the order of the field enters: the surviving
inequations force `g` to be primitive and then compare `g⁻⁶` with `g⁹`. -/
theorem pins_collide : ∀ c g : F16, c ≠ 0 → g ≠ 0 →
    Collide (pinsL c g) ∨ Collide (pinsL2 c g) := by decide

/-- An injective map cannot realize a colliding list of values. -/
theorem not_collide {L : F16 → F16} (hinj : Function.Injective L) {l : List (F16 × F16)}
    (h : ∀ p ∈ l, L p.1 = p.2) : ¬ Collide l := by
  rintro ⟨p, hp, q, hq, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
  · exact h2 (by rw [← h p hp, ← h q hq, h1])
  · exact h1 (hinj (by rw [h p hp, h q hq, h2]))

/-! ### The obstruction, with the magma eliminated -/

/-- **The heart of the argument.** No self-map of `F₁₆` satisfies the three consequences that law
`467` imposes on a homogeneous operation. -/
theorem no_perm (L : F16 → F16) (c g s : F16) (hL0 : L 0 = s) (hL1 : L 1 = c)
    (hA : ∀ x : F16, x ≠ 0 → L (x * L (L (c * x⁻¹))) = x)
    (hB : L s * g = 1) (hC : L (c * (g * g)) = 0) : False := by
  -- the three parameters are nonzero
  have hg : g ≠ 0 := by rintro rfl; simp at hB
  have hs : s ≠ 0 := by rintro rfl; rw [hL0] at hB; simp at hB
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_mul, hL0] at hC
    exact hs hC
  have hLs : L s = g⁻¹ := eq_inv_of_mul_eq_one_left hB
  -- `L` is onto, hence a permutation
  have hsurj : Function.Surjective L := by
    intro y
    by_cases hy : y = 0
    · exact ⟨c * (g * g), by rw [hC, hy]⟩
    · exact ⟨y * L (L (c * y⁻¹)), hA y hy⟩
  have hinj : Function.Injective L := Finite.injective_iff_surjective.2 hsurj
  have hinj2 : Function.Injective (fun x ↦ L (L x)) := hinj.comp hinj
  -- `L²` kills `c / s`
  have hLLcs : L (L (c * s⁻¹)) = 0 := by
    have h := hA s hs
    have h2 : s * L (L (c * s⁻¹)) = 0 := hinj (by rw [h, hL0])
    simpa [hs] using h2
  -- (D), by a product count over the fourteen `x` outside `{0, s}`
  have hD : s = c * (g * g * g) := by
    have hcg2 : c * (g * g) ≠ 0 := by simp [hc, hg]
    have hginv : (g⁻¹ : F16) ≠ 0 := inv_ne_zero hg
    -- the two reindexings
    have r1 : ∏ x ∈ univ \ ({0, s} : Finset F16), (x * L (L (c * x⁻¹)))
        = ∏ y ∈ univ \ ({0, c * (g * g)} : Finset F16), y := by
      refine prod_reindex (Ne.symm hs) (Ne.symm hcg2) ?_ ?_ ?_
      · intro x hx y hy hxy
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
        rw [← hA x hx.2.1, ← hA y hy.2.1, hxy]
      · intro x hx hx0
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hx.2.2 (by rw [← hA x hx.2.1, hx0, hL0])
      · intro x hx hxv
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hx.2.1 (by rw [← hA x hx.2.1, hxv, hC])
    have r2 : ∏ x ∈ univ \ ({0, s} : Finset F16), L (L (c * x⁻¹))
        = ∏ y ∈ univ \ ({0, g⁻¹} : Finset F16), y := by
      refine prod_reindex (Ne.symm hs) (Ne.symm hginv) ?_ ?_ ?_
      · intro x _ y _ hxy
        exact inv_injective (mul_left_cancel₀ hc (hinj2 hxy))
      · intro x hx hx0
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hx.2.2 (inv_injective (mul_left_cancel₀ hc (hinj2 (hx0.trans hLLcs.symm))))
      · intro x hx hxv
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have h0 : L (L (0 : F16)) = g⁻¹ := by rw [hL0, hLs]
        rcases mul_eq_zero.1 (hinj2 (hxv.trans h0.symm)) with h' | h'
        · exact hc h'
        · exact hx.2.1 (inv_eq_zero.1 h')
    -- put the three products together
    rw [Finset.prod_mul_distrib, F16.prod_sdiff_pair hs, r2, F16.prod_sdiff_pair hginv,
      F16.prod_sdiff_pair hcg2, inv_inv] at r1
    field_simp at r1
    rw [← r1]
    ring
  -- the nine values of `L`
  have p1 : L 0 = c * (g * g * g) := by rw [hL0, hD]
  have p5 : L (c * (g * g)) = 0 := hC
  have p6 : L (c * (g * g * g)) = g⁻¹ := by rw [← hD]; exact hLs
  have p3 : L c = c⁻¹ := by
    have h := hA c hc
    rw [mul_inv_cancel₀ hc, hL1] at h
    have h2 : c * L c = 1 := hinj (by rw [h, hL1])
    exact eq_inv_of_mul_eq_one_right h2
  have p9 : L ((g * g * g)⁻¹) = c * (g * g) := by
    have e : c * s⁻¹ = ((g * g * g) : F16)⁻¹ := by rw [hD]; field_simp
    rw [← e]
    exact hinj (by rw [hLLcs, hC])
  have p4 : L (c * g) = (g * g)⁻¹ := by
    have hx : ((g * g : F16)⁻¹) ≠ 0 := inv_ne_zero (by simp [hg])
    have h := hA _ hx
    rw [inv_inv, hC, hL0, hD,
      show ((g * g : F16)⁻¹) * (c * (g * g * g)) = c * g from by field_simp] at h
    exact h
  have p8 : L ((g * g)⁻¹) = c * (g * g * g * g) := by
    have h := hA g⁻¹ (inv_ne_zero hg)
    rw [inv_inv, p4] at h
    have h2 : g⁻¹ * L ((g * g)⁻¹) = c * (g * g * g) := hinj (by rw [h, p6])
    rw [solve (inv_ne_zero hg) h2, inv_inv]
    ring
  have p7 : L (c * (g * g * g * g)) = (c * (g * g * g * g * g))⁻¹ := by
    have hx : c * (g * g) ≠ 0 := by simp [hc, hg]
    have h := hA _ hx
    rw [show c * (c * (g * g) : F16)⁻¹ = ((g * g : F16)⁻¹) from by field_simp, p8] at h
    have h2 : c * (g * g) * L (c * (g * g * g * g)) = ((g * g * g : F16)⁻¹) :=
      hinj (by rw [h, p9])
    rw [solve hx h2]
    field_simp
  -- the three values of `L²`
  have q1 : L (L 1) = c⁻¹ := by rw [hL1, p3]
  have q2 : L (L (c * c * (g * g * g * g * g)))
      = c * c * (g * g * g * g * g * g * g * g * g) := by
    have hx : ((c * (g * g * g * g * g) : F16)⁻¹) ≠ 0 := inv_ne_zero (by simp [hc, hg])
    have h := hA _ hx
    rw [inv_inv, show c * (c * (g * g * g * g * g)) = c * c * (g * g * g * g * g) from by ring] at h
    have h2 : ((c * (g * g * g * g * g) : F16)⁻¹) * L (L (c * c * (g * g * g * g * g)))
        = c * (g * g * g * g) := hinj (by rw [h, p7])
    rw [solve hx h2, inv_inv]
    ring
  have q3 : L (L ((g * g * g * g)⁻¹)) = (c * (g * g * g * g * g * g))⁻¹ := by
    have hx : c * (g * g * g * g) ≠ 0 := by simp [hc, hg]
    have h := hA _ hx
    rw [show c * (c * (g * g * g * g) : F16)⁻¹ = ((g * g * g * g : F16)⁻¹) from by
      field_simp] at h
    have h2 : c * (g * g * g * g) * L (L ((g * g * g * g)⁻¹)) = ((g * g : F16)⁻¹) :=
      hinj (by rw [h, p8])
    rw [solve hx h2]
    field_simp
  -- no `(c, g)` survives
  rcases pins_collide c g hc hg with h | h
  · refine not_collide hinj (fun p hp ↦ ?_) h
    simp only [pinsL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [p1, hL1, p3, p4, p5, p6, p7, p8, p9]
  · refine not_collide hinj2 (fun p hp ↦ ?_) h
    simp only [pinsL2, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    exacts [q1, q2, q3]


/-! ### From the law on a magma to those three consequences -/

/-- Homogeneity follows from the *single* scalar `t`, because `t` generates `F₁₆ˣ`. This is what
lets a one-automorphism obstruction do the work of the whole group. -/
theorem homog_of_t {W : F16 → F16 → F16}
    (h : ∀ x y : F16, W (F16.t * x) (F16.t * y) = F16.t * W x y) : Homog W := by
  have hpow : ∀ (n : ℕ) (x y : F16),
      W (F16.t ^ n * x) (F16.t ^ n * y) = F16.t ^ n * W x y := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ k ih =>
      intro x y
      have e : (F16.t) ^ (k + 1) = F16.t * F16.t ^ k := by rw [pow_succ, mul_comm]
      rw [e, mul_assoc, mul_assoc, h, ih, ← mul_assoc]
  intro a x y ha
  obtain ⟨n, hn⟩ := F16.exists_pow_t a ha
  rw [← hn]
  exact hpow n x y

/-- **The obstruction.** No homogeneous operation on `F₁₆` satisfies law `467`. -/
theorem no_homog_467 (W : F16 → F16 → F16) (hW : Homog W)
    (h467 : ∀ x y : F16, x = W y (W x (W x (W y y)))) : False := by
  -- `W` restricted to the two orbits of the scalar action
  have hz : W 0 0 = 0 := by
    have h2 := hW F16.t 0 0 F16.t_ne_zero
    rw [mul_zero] at h2
    have h3 : (F16.t - 1) * W 0 0 = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h' | h'
    · exact absurd h' F16.t_sub_one_ne_zero
    · exact h'
  have hlz : ∀ y : F16, W 0 y = y * W 0 1 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [hz, zero_mul]
    · have h := hW y 0 1 hy
      rwa [mul_zero, mul_one] at h
  have hgen : ∀ x y : F16, x ≠ 0 → W x y = x * W 1 (x⁻¹ * y) := by
    intro x y hx
    have h := hW x 1 (x⁻¹ * y) hx
    rwa [mul_one, mul_inv_cancel_left₀ hx] at h
  refine no_perm (fun v ↦ W 1 v) (W 1 1) (W 0 1) (W 1 0) rfl rfl ?_ ?_ ?_
  · -- (A), from the law at `(x, 1)` with `x ≠ 0`
    intro x hx
    have h := h467 x 1
    rw [hgen x (W 1 1) hx, hgen x _ hx, inv_mul_cancel_left₀ hx] at h
    show W 1 (x * W 1 (W 1 (W 1 1 * x⁻¹))) = x
    rw [mul_comm (W 1 1) x⁻¹]
    exact h.symm
  · -- (B), from the law at `(1, 0)`
    have h := h467 1 0
    rw [hz, hlz (W 1 (W 1 0))] at h
    show W 1 (W 1 0) * W 0 1 = 1
    exact h.symm
  · -- (C), from the law at `(0, 1)`
    have h := h467 0 1
    rw [hlz (W 0 (W 1 1)), hlz (W 1 1)] at h
    show W 1 (W 1 1 * (W 0 1 * W 0 1)) = 0
    rw [← mul_assoc]
    exact h.symm

/-- The same for law `3140`, `x = (((y ◇ y) ◇ x) ◇ x) ◇ y`, which is `467` in the opposite magma:
the opposite of a homogeneous operation is homogeneous. -/
theorem no_homog_3140 (W : F16 → F16 → F16) (hW : Homog W)
    (h3140 : ∀ x y : F16, x = W (W (W (W y y) x) x) y) : False :=
  no_homog_467 (fun x y ↦ W y x) (fun a x y ha ↦ hW a y x ha) h3140

/-! ### The models, and the four cells they close -/

/-- The linear model `x ◇ y = t⁵ x + t² y` of law `1516` on `F₁₆`. -/
@[implicit_reducible]
def mag1516 : Magma F16 := ⟨fun x y ↦ F16.t ^ 5 * x + F16.t ^ 2 * y⟩

/-- The opposite magma, `x ◇ y = t² x + t⁵ y`, a model of law `2091`. -/
@[implicit_reducible]
def mag2091 : Magma F16 := ⟨fun x y ↦ F16.t ^ 2 * x + F16.t ^ 5 * y⟩

theorem mag1516_satisfies : @Equation1516 F16 mag1516 := by decide!

theorem mag2091_satisfies : @Equation2091 F16 mag2091 := by decide!

/-- Multiplication by the primitive root `t`, as a permutation of `F₁₆`. -/
def scale : F16 ≃ F16 where
  toFun x := F16.t * x
  invFun x := F16.t⁻¹ * x
  left_inv x := inv_mul_cancel_left₀ F16.t_ne_zero x
  right_inv x := mul_inv_cancel_left₀ F16.t_ne_zero x

theorem mag1516_isEndo : mag1516.IsEndo ⇑scale := by
  intro x y
  show F16.t * (F16.t ^ 5 * x + F16.t ^ 2 * y)
    = F16.t ^ 5 * (F16.t * x) + F16.t ^ 2 * (F16.t * y)
  ring

theorem mag2091_isEndo : mag2091.IsEndo ⇑scale := by
  intro x y
  show F16.t * (F16.t ^ 2 * x + F16.t ^ 5 * y)
    = F16.t ^ 2 * (F16.t * x) + F16.t ^ 5 * (F16.t * y)
  ring

end Hom467

open Hom467

theorem Equation467_not_definableFrom_Equation1516 : ¬ Law467.DefinableFrom Law1516 :=
  not_definableFrom_of_isAuto mag1516 ((@Law1516.models_iff F16 mag1516).mpr mag1516_satisfies)
    mag1516_isEndo fun M' hM' hendo ↦
      no_homog_467 M'.op (homog_of_t fun x y ↦ (hendo x y).symm)
        ((@Law467.models_iff F16 M').mp hM')

theorem Equation3140_not_definableFrom_Equation1516 : ¬ Law3140.DefinableFrom Law1516 :=
  not_definableFrom_of_isAuto mag1516 ((@Law1516.models_iff F16 mag1516).mpr mag1516_satisfies)
    mag1516_isEndo fun M' hM' hendo ↦
      no_homog_3140 M'.op (homog_of_t fun x y ↦ (hendo x y).symm)
        ((@Law3140.models_iff F16 M').mp hM')

theorem Equation467_not_definableFrom_Equation2091 : ¬ Law467.DefinableFrom Law2091 :=
  not_definableFrom_of_isAuto mag2091 ((@Law2091.models_iff F16 mag2091).mpr mag2091_satisfies)
    mag2091_isEndo fun M' hM' hendo ↦
      no_homog_467 M'.op (homog_of_t fun x y ↦ (hendo x y).symm)
        ((@Law467.models_iff F16 M').mp hM')

theorem Equation3140_not_definableFrom_Equation2091 : ¬ Law3140.DefinableFrom Law2091 :=
  not_definableFrom_of_isAuto mag2091 ((@Law2091.models_iff F16 mag2091).mpr mag2091_satisfies)
    mag2091_isEndo fun M' hM' hendo ↦
      no_homog_3140 M'.op (homog_of_t fun x y ↦ (hendo x y).symm)
        ((@Law3140.models_iff F16 M').mp hM')
