import equational_theories.Definability.LinearGaussian

/-!
# The cover of the Gaussian certificates

The `11` non-definability facts stated by the three models of `Definability/LinearGaussian.lean`.
Under the implications of the board they close `362` open cells that no certificate in
`Definability/` reaches, on top of the `184` already carried by `Definability/LinearIntCover.lean`
— together `546` of the `946` that only an infinite linear model can settle.

Each model contributes one source equation against a handful of targets, because coverage
factorises: a cell `(t, s)` follows from a stated cell `(t', s')` as soon as `t' ⊢ t` and `s ⊢ s'`
separately, so the target list and the source list are two independent hitting sets and only their
product has to be written down.

The statements refute `TermDefinableFrom`, and only over all magmas; see the module docstring of
`Definability/LinearGaussian.lean`.
-/

open Law.MagmaLaw Magma

local notation "ℤ[i]" => GaussianInt

/-! ### Model A: `x ◇ y = -x - i * y`, against equation `546` -/

theorem Equation3269_not_termDefinableFrom_Equation546 :
    ¬ Law3269.TermDefinableFrom Law546 :=
  not_termDefinableFrom_of_lin (-1) (-gi) (-2 - gi) 1 (by ring)
    ((@Law546.models_iff ℤ[i] (lin (-1) (-gi))).mpr giA_satisfies_546)
    fun α γ h ↦ linFam_not_3269 _ α γ giA_hc gi_ne_3269
      ((@Law3269.models_iff ℤ[i] (linFam (-2 - gi) α γ)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation546 :
    ¬ Law3279.TermDefinableFrom Law546 :=
  not_termDefinableFrom_of_lin (-1) (-gi) (-2 - gi) 1 (by ring)
    ((@Law546.models_iff ℤ[i] (lin (-1) (-gi))).mpr giA_satisfies_546)
    fun α γ h ↦ linFam_not_3279 _ α γ giA_hc gi_ne_3279
      ((@Law3279.models_iff ℤ[i] (linFam (-2 - gi) α γ)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation546 :
    ¬ Law3475.TermDefinableFrom Law546 :=
  not_termDefinableFrom_of_lin (-1) (-gi) (-2 - gi) 1 (by ring)
    ((@Law546.models_iff ℤ[i] (lin (-1) (-gi))).mpr giA_satisfies_546)
    fun α γ h ↦ linFam_not_3475 _ α γ giA_hc gi_ne_3475
      ((@Law3475.models_iff ℤ[i] (linFam (-2 - gi) α γ)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation546 :
    ¬ Law3482.TermDefinableFrom Law546 :=
  not_termDefinableFrom_of_lin (-1) (-gi) (-2 - gi) 1 (by ring)
    ((@Law546.models_iff ℤ[i] (lin (-1) (-gi))).mpr giA_satisfies_546)
    fun α γ h ↦ linFam_not_3482 _ α γ giA_hc gi_ne_3279 gi_ne_quad
      ((@Law3482.models_iff ℤ[i] (linFam (-2 - gi) α γ)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation546 :
    ¬ Law3675.TermDefinableFrom Law546 :=
  not_termDefinableFrom_of_lin (-1) (-gi) (-2 - gi) 1 (by ring)
    ((@Law546.models_iff ℤ[i] (lin (-1) (-gi))).mpr giA_satisfies_546)
    fun α γ h ↦ linFam_not_3675 _ α γ giA_hc gi_ne_3675
      ((@Law3675.models_iff ℤ[i] (linFam (-2 - gi) α γ)).mp h)

/-! ### Model B: `x ◇ y = -i * x - i * y`, against equation `556` -/

theorem Equation3269_not_termDefinableFrom_Equation556 :
    ¬ Law3269.TermDefinableFrom Law556 :=
  not_termDefinableFrom_of_lin (-gi) (-gi) (-1 - 2 * gi) 1 (by ring)
    ((@Law556.models_iff ℤ[i] (lin (-gi) (-gi))).mpr giB_satisfies_556)
    fun α γ h ↦ linFam_not_3269 _ α γ giB_hc gi_ne_3269
      ((@Law3269.models_iff ℤ[i] (linFam (-1 - 2 * gi) α γ)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation556 :
    ¬ Law3279.TermDefinableFrom Law556 :=
  not_termDefinableFrom_of_lin (-gi) (-gi) (-1 - 2 * gi) 1 (by ring)
    ((@Law556.models_iff ℤ[i] (lin (-gi) (-gi))).mpr giB_satisfies_556)
    fun α γ h ↦ linFam_not_3279 _ α γ giB_hc gi_ne_3279
      ((@Law3279.models_iff ℤ[i] (linFam (-1 - 2 * gi) α γ)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation556 :
    ¬ Law3475.TermDefinableFrom Law556 :=
  not_termDefinableFrom_of_lin (-gi) (-gi) (-1 - 2 * gi) 1 (by ring)
    ((@Law556.models_iff ℤ[i] (lin (-gi) (-gi))).mpr giB_satisfies_556)
    fun α γ h ↦ linFam_not_3475 _ α γ giB_hc gi_ne_3475
      ((@Law3475.models_iff ℤ[i] (linFam (-1 - 2 * gi) α γ)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation556 :
    ¬ Law3482.TermDefinableFrom Law556 :=
  not_termDefinableFrom_of_lin (-gi) (-gi) (-1 - 2 * gi) 1 (by ring)
    ((@Law556.models_iff ℤ[i] (lin (-gi) (-gi))).mpr giB_satisfies_556)
    fun α γ h ↦ linFam_not_3482 _ α γ giB_hc gi_ne_3279 gi_ne_quad
      ((@Law3482.models_iff ℤ[i] (linFam (-1 - 2 * gi) α γ)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation556 :
    ¬ Law3675.TermDefinableFrom Law556 :=
  not_termDefinableFrom_of_lin (-gi) (-gi) (-1 - 2 * gi) 1 (by ring)
    ((@Law556.models_iff ℤ[i] (lin (-gi) (-gi))).mpr giB_satisfies_556)
    fun α γ h ↦ linFam_not_3675 _ α γ giB_hc gi_ne_3675
      ((@Law3675.models_iff ℤ[i] (linFam (-1 - 2 * gi) α γ)).mp h)

/-! ### Model C: `x ◇ y = (-1 - i) * x - 2 * i * y`, against equation `4588` -/

theorem Equation3472_not_termDefinableFrom_Equation4588 :
    ¬ Law3472.TermDefinableFrom Law4588 :=
  not_termDefinableFrom_of_lin (-1 - gi) (-2 * gi) (-2 - 3 * gi) 1 (by ring)
    ((@Law4588.models_iff ℤ[i] (lin (-1 - gi) (-2 * gi))).mpr giC_satisfies_4588)
    fun α γ h ↦ linFam_not_3472 _ α γ giC_hc gi_ne_3472 giC_h3
      ((@Law3472.models_iff ℤ[i] (linFam (-2 - 3 * gi) α γ)).mp h)
