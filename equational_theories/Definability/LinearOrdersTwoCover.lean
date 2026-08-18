import equational_theories.Definability.LinearOrdersTwo

/-!
# The definability cell `2` not being a unit closes

One application of `Magma.not_termDefinableFrom_of_lin`, exactly as in
`Definability/LinearOrdersCover.lean`, but through `Magma.linFam_not_3272'`.
-/

open Law.MagmaLaw Magma

theorem Equation3272_not_termDefinableFrom_Equation1083 :
    ¬ Law3272.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_lin (-CubicC.th ^ 2 - 1) (CubicC.th)
    (-CubicC.th ^ 2 + CubicC.th - 2) 1 (by ring)
    ((@Law1083.models_iff CubicC.R (lin (-CubicC.th ^ 2 - 1) (CubicC.th))).mpr
      CubicC.sat_1083)
    fun α γ h ↦ linFam_not_3272' _ α γ CubicC.hc CubicC.hP3678 CubicC.hc₂
      ((@Law3272.models_iff CubicC.R
        (linFam (-CubicC.th ^ 2 + CubicC.th - 2) α γ)).mp h)
