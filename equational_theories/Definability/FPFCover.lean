import equational_theories.Definability.FPF

/-!
# The fixed-point-free cover

Three applications of `Law.MagmaLaw.not_definableFrom_of_fixedPointFree`, all with the same target
`4482` and the same automorphism `Fin.xorPerm8 1`. Being automorphism arguments they refute
first-order definability, hence also term-definability, over all magmas.
-/

open Law Law.MagmaLaw Magma

theorem Equation4482_not_definableFrom_Equation3342 : ¬ Law4482.DefinableFrom Law3342 :=
  not_definableFrom_of_fixedPointFree fpfCert3342
    ((@Law3342.models_iff (Fin 8) fpfCert3342).mpr fpfCert3342_satisfies)
    fpfCert3342_isEndo xorPerm8_one_ne
    fun M' hM' hendo ↦ exists_fixed_of_4482 M'
      ((@Law4482.models_iff (Fin 8) M').mp hM') xorPerm8_one_involutive hendo 0

theorem Equation4482_not_definableFrom_Equation3545 : ¬ Law4482.DefinableFrom Law3545 :=
  not_definableFrom_of_fixedPointFree fpfCert3545
    ((@Law3545.models_iff (Fin 8) fpfCert3545).mpr fpfCert3545_satisfies)
    fpfCert3545_isEndo xorPerm8_one_ne
    fun M' hM' hendo ↦ exists_fixed_of_4482 M'
      ((@Law4482.models_iff (Fin 8) M').mp hM') xorPerm8_one_involutive hendo 0

theorem Equation4482_not_definableFrom_Equation4415 : ¬ Law4482.DefinableFrom Law4415 :=
  not_definableFrom_of_fixedPointFree fpfCert4415
    ((@Law4415.models_iff (Fin 8) fpfCert4415).mpr fpfCert4415_satisfies)
    fpfCert4415_isEndo xorPerm8_one_ne
    fun M' hM' hendo ↦ exists_fixed_of_4482 M'
      ((@Law4482.models_iff (Fin 8) M').mp hM') xorPerm8_one_involutive hendo 0
