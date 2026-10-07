import equational_theories.Definability.FreeGroupUnaryRecovery

/-!
# Two E73 operations with the same erased diagonal

The existing free-group extension theorem accepts a ten-pair seed. Its total
function `f` satisfies E73, has no fixed point, and never evaluates the outer
`f` of the functional identity at `1`. Consequently we may replace `f(1)` by
a second prescribed three-cycle without changing the identity.

The associated operations `f(y*x⁻¹)*x` agree whenever `x≠y`, but disagree at
every diagonal entry. Thus diagonal erasure is not injective on infinite E73
models, and no single restoration map can work for all such models.
This is an obstruction to that method, not a refutation of arbitrary
FO-structural interpretation into E3.
-/

namespace E63Family.Homogeneous
variable {G : Type} [Group G]

theorem equation73_iff (f : G → G) :
    @Equation73 G ⟨op f⟩ ↔ ∀ x, f (f (f x * x⁻¹)) = x⁻¹ := by
  constructor
  · intro h x
    simpa [op] using (h x⁻¹ 1).symm
  · intro h x y
    change x = op f y (op f y (op f x y))
    simp only [op]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    have hh := h (y*x⁻¹)
    simp only [mul_inv_rev, inv_inv] at hh
    rw [hh]
    group

open scoped Classical in
noncomputable def switchOne (f : G → G) (b x : G) := if x=1 then b else f x

theorem switchOne_eq73 (f : G → G)
    (h : ∀ x, f (f (f x*x⁻¹)) = x⁻¹)
    (hfix : ∀ x, f x ≠ x) (houter : ∀ x, f (f x*x⁻¹) ≠ 1)
    (b d : G) (hb : b ≠ 1) (hd : d ≠ 1) (hbd : f b = d) (hd1 : f d = 1) :
    ∀ x, switchOne f b (switchOne f b (switchOne f b x*x⁻¹)) = x⁻¹ := by
  intro x
  by_cases hx : x=1
  · subst x
    simp [switchOne, hb, hd, hbd, hd1]
  · have hr : f x*x⁻¹ ≠ 1 := fun he => hfix x (eq_of_mul_inv_eq_one he)
    simp only [switchOne, hx, if_false, hr, houter x]
    exact h x

theorem no_fixed_of_seed (f : G → G) (h : ∀ x, f (f (f x*x⁻¹)) = x⁻¹)
    (a c : G) (h1 : f 1=a) (ha : f a=c) (hc : f c⁻¹ ≠ c⁻¹) : ∀ x, f x ≠ x := by
  intro x hx
  have hh := h x
  rw [hx, mul_inv_cancel, h1, ha] at hh
  have he : x=c⁻¹ := by rw [hh, inv_inv]
  exact hc (he ▸ hx)

theorem no_outer_one_of_seed (f : G → G) (h : ∀ x, f (f (f x*x⁻¹)) = x⁻¹)
    (a : G) (h1 : f 1=a) (ha : f (f a⁻¹*a) ≠ 1) :
    ∀ x, f (f x*x⁻¹) ≠ 1 := by
  intro x hx
  have hh := h x
  rw [hx, h1] at hh
  have he : x=a⁻¹ := by rw [hh, inv_inv]
  subst x
  exact ha (by simpa only [inv_inv] using hx)

end E63Family.Homogeneous

namespace E73DiagonalAmbiguity
open Eq73.Greedy E63Family.Homogeneous
abbrev G := FreeGroup ℕ
private abbrev g (n : ℕ) : G := FreeGroup.of n

def seed : List (G × G) := E0List ++
  [(g 3,g 4),(g 4,1),((g 2)⁻¹,g 5),(g 5,(g 2)⁻¹),
   ((g 1)⁻¹,g 7),(g 7*g 1,g 8),(g 8,g 1)]

noncomputable def extension : Extension := ⟨fromList seed, fromList_ok⟩
noncomputable def f₀ : G → G := Eq73.Greedy.f extension
noncomputable def f₁ : G → G := switchOne f₀ (g 3)

lemma eval_seed (x y : G) (h : (x,y) ∈ seed) : f₀ x = y :=
  fromList_eval rfl x y h

lemma f₀_eq73 : ∀ x, f₀ (f₀ (f₀ x*x⁻¹)) = x⁻¹ := f_eq73 extension

lemma f₀_one : f₀ 1 = g 1 := eval_seed _ _ (by decide)
lemma f₀_no_fixed : ∀ x, f₀ x ≠ x := by
  apply no_fixed_of_seed f₀ f₀_eq73 (g 1) (g 2) f₀_one
    (eval_seed _ _ (by decide))
  rw [eval_seed ((g 2)⁻¹) (g 5) (by decide)]
  decide

lemma f₀_no_outer_one : ∀ x, f₀ (f₀ x*x⁻¹) ≠ 1 := by
  apply no_outer_one_of_seed f₀ f₀_eq73 (g 1) f₀_one
  rw [eval_seed ((g 1)⁻¹) (g 7) (by decide),
    eval_seed (g 7*g 1) (g 8) (by decide)]
  decide

lemma f₁_eq73 : ∀ x, f₁ (f₁ (f₁ x*x⁻¹)) = x⁻¹ :=
  switchOne_eq73 f₀ f₀_eq73 f₀_no_fixed f₀_no_outer_one (g 3) (g 4)
    (by decide) (by decide) (eval_seed _ _ (by decide)) (eval_seed _ _ (by decide))

@[reducible] noncomputable def first : Magma G := ⟨E63Family.Homogeneous.op f₀⟩
@[reducible] noncomputable def second : Magma G := ⟨E63Family.Homogeneous.op f₁⟩

lemma first_equation73 : @Equation73 G first := (equation73_iff f₀).mpr f₀_eq73
lemma second_equation73 : @Equation73 G second := (equation73_iff f₁).mpr f₁_eq73

lemma agree_off_diagonal (x y : G) (h : x ≠ y) : first.op x y = second.op x y := by
  have hr : y*x⁻¹ ≠ 1 := fun he => h (eq_of_mul_inv_eq_one he).symm
  change E63Family.Homogeneous.op f₀ x y = E63Family.Homogeneous.op f₁ x y
  simp only [E63Family.Homogeneous.op, f₁, switchOne, hr, if_false]

lemma disagree_on_diagonal (x : G) : first.op x x ≠ second.op x x := by
  change E63Family.Homogeneous.op f₀ x x ≠ E63Family.Homogeneous.op f₁ x x
  simp only [E63Family.Homogeneous.op, mul_inv_cancel, f₀_one,
    f₁, switchOne]
  intro h
  have hh := mul_right_cancel h
  exact (by decide : g 1 ≠ g 3) hh

open scoped Classical in
@[reducible] noncomputable def eraseDiagonal (M : Magma G) : Magma G :=
  ⟨fun x y => if x=y then x else M.op x y⟩

lemma erased_equal : eraseDiagonal first = eraseDiagonal second := by
  unfold eraseDiagonal
  congr 1
  funext x y
  by_cases h : x=y
  · simp [h]
  · simp [h,agree_off_diagonal x y h]

/-- There is no single restoration map from erased E73 tables to original tables.
This does not rule out other FO companions, or model-dependent recovery formulas. -/
theorem no_uniform_recovery : ¬ ∃ restore : Magma G → Magma G,
    ∀ M : Magma G, @Equation73 G M → restore (eraseDiagonal M) = M := by
  rintro ⟨restore,h⟩
  have h₀ := h first first_equation73
  have h₁ := h second second_equation73
  rw [erased_equal] at h₀
  have he : first = second := h₀.symm.trans h₁
  exact disagree_on_diagonal 1 (congrArg (fun M : Magma G => M.op 1 1) he)

end E73DiagonalAmbiguity

spectrum_assert E73DiagonalAmbiguity.first_equation73 complete
spectrum_assert E73DiagonalAmbiguity.second_equation73 complete
spectrum_assert E73DiagonalAmbiguity.agree_off_diagonal complete
spectrum_assert E73DiagonalAmbiguity.disagree_on_diagonal complete

spectrum_assert E73DiagonalAmbiguity.no_uniform_recovery complete
