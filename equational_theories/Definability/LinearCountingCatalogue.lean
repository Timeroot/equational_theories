import equational_theories.Definability.LinearCounting

/-!
# Finite product certificates from linear-model counts

Every source factor is checked on its field, and every target coefficient pair
is tested at the six basis assignments. The product carriers are never enumerated.
These refute finite term-structural definability, not term-definability without
recovery or first-order structural definability. Ten generators cover the
21 completely-open class pairs sourced at E704, E1276, and E1279.
-/

open Law Law.MagmaLaw Magma

/-- A product of 2 distinct linear E1276 models over `ZMod 5` has too few
linear E680 companions to admit term recovery. -/
theorem Equation680_not_termStructuralFromFin_Equation1276_linearCount :
    ¬ Law680.TermStructuralFromFin Law1276 := by
  apply not_termStructuralFromFin_of_linear_count
    (![1, 4] : Fin 2 → ZMod 5) (![3, 4] : Fin 2 → ZMod 5)
  · decide
  · intro i
    apply (@Law1276.models_iff (ZMod 5) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation680_not_termStructuralFromFin_Equation1276_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation680_not_termStructuralFromFin_Equation1276_linearCount._native.native_decide.ax_1_1,
Equation680_not_termStructuralFromFin_Equation1276_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation680_not_termStructuralFromFin_Equation1276_linearCount

/-- A product of 2 distinct linear E1276 models over `ZMod 23` has too few
linear E707 companions to admit term recovery. -/
theorem Equation707_not_termStructuralFromFin_Equation1276_linearCount :
    ¬ Law707.TermStructuralFromFin Law1276 := by
  apply not_termStructuralFromFin_of_linear_count
    (![10, 11] : Fin 2 → ZMod 23) (![6, 14] : Fin 2 → ZMod 23)
  · decide
  · intro i
    apply (@Law1276.models_iff (ZMod 23) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation707_not_termStructuralFromFin_Equation1276_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation707_not_termStructuralFromFin_Equation1276_linearCount._native.native_decide.ax_1_1,
Equation707_not_termStructuralFromFin_Equation1276_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation707_not_termStructuralFromFin_Equation1276_linearCount

/-- A product of 2 distinct linear E704 models over `ZMod 47` has too few
linear E504 companions to admit term recovery. -/
theorem Equation504_not_termStructuralFromFin_Equation704_linearCount :
    ¬ Law504.TermStructuralFromFin Law704 := by
  apply not_termStructuralFromFin_of_linear_count
    (![7, 4] : Fin 2 → ZMod 47) (![9, 20] : Fin 2 → ZMod 47)
  · decide
  · intro i
    apply (@Law704.models_iff (ZMod 47) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation504_not_termStructuralFromFin_Equation704_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation504_not_termStructuralFromFin_Equation704_linearCount._native.native_decide.ax_1_1,
Equation504_not_termStructuralFromFin_Equation704_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation504_not_termStructuralFromFin_Equation704_linearCount

/-- A product of 4 distinct linear E704 models over `ZMod 83` has too few
linear E870 companions to admit term recovery. -/
theorem Equation870_not_termStructuralFromFin_Equation704_linearCount :
    ¬ Law870.TermStructuralFromFin Law704 := by
  apply not_termStructuralFromFin_of_linear_count
    (![9, 76, 40, 42] : Fin 4 → ZMod 83) (![7, 42, 44, 63] : Fin 4 → ZMod 83)
  · decide
  · intro i
    apply (@Law704.models_iff (ZMod 83) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation870_not_termStructuralFromFin_Equation704_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation870_not_termStructuralFromFin_Equation704_linearCount._native.native_decide.ax_1_1,
Equation870_not_termStructuralFromFin_Equation704_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation870_not_termStructuralFromFin_Equation704_linearCount

/-- A product of 2 distinct linear E704 models over `ZMod 47` has too few
linear E917 companions to admit term recovery. -/
theorem Equation917_not_termStructuralFromFin_Equation704_linearCount :
    ¬ Law917.TermStructuralFromFin Law704 := by
  apply not_termStructuralFromFin_of_linear_count
    (![7, 4] : Fin 2 → ZMod 47) (![9, 20] : Fin 2 → ZMod 47)
  · decide
  · intro i
    apply (@Law704.models_iff (ZMod 47) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation917_not_termStructuralFromFin_Equation704_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation917_not_termStructuralFromFin_Equation704_linearCount._native.native_decide.ax_1_1,
Equation917_not_termStructuralFromFin_Equation704_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation917_not_termStructuralFromFin_Equation704_linearCount

/-- A product of 3 distinct linear E1279 models over `ZMod 67` has too few
linear E504 companions to admit term recovery. -/
theorem Equation504_not_termStructuralFromFin_Equation1279_linearCount :
    ¬ Law504.TermStructuralFromFin Law1279 := by
  apply not_termStructuralFromFin_of_linear_count
    (![26, 56, 19] : Fin 3 → ZMod 67) (![2, 35, 49] : Fin 3 → ZMod 67)
  · decide
  · intro i
    apply (@Law1279.models_iff (ZMod 67) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation504_not_termStructuralFromFin_Equation1279_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation504_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_1,
Equation504_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation504_not_termStructuralFromFin_Equation1279_linearCount

/-- A product of 3 distinct linear E1279 models over `ZMod 29` has too few
linear E870 companions to admit term recovery. -/
theorem Equation870_not_termStructuralFromFin_Equation1279_linearCount :
    ¬ Law870.TermStructuralFromFin Law1279 := by
  apply not_termStructuralFromFin_of_linear_count
    (![10, 4, 23] : Fin 3 → ZMod 29) (![6, 11, 14] : Fin 3 → ZMod 29)
  · decide
  · intro i
    apply (@Law1279.models_iff (ZMod 29) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation870_not_termStructuralFromFin_Equation1279_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation870_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_1,
Equation870_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation870_not_termStructuralFromFin_Equation1279_linearCount

/-- A product of 3 distinct linear E1279 models over `ZMod 67` has too few
linear E917 companions to admit term recovery. -/
theorem Equation917_not_termStructuralFromFin_Equation1279_linearCount :
    ¬ Law917.TermStructuralFromFin Law1279 := by
  apply not_termStructuralFromFin_of_linear_count
    (![26, 56, 19] : Fin 3 → ZMod 67) (![2, 35, 49] : Fin 3 → ZMod 67)
  · decide
  · intro i
    apply (@Law1279.models_iff (ZMod 67) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation917_not_termStructuralFromFin_Equation1279_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation917_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_1,
Equation917_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation917_not_termStructuralFromFin_Equation1279_linearCount

/-- A product of 3 distinct linear E1279 models over `ZMod 29` has too few
linear E3345 companions to admit term recovery. -/
theorem Equation3345_not_termStructuralFromFin_Equation1279_linearCount :
    ¬ Law3345.TermStructuralFromFin Law1279 := by
  apply not_termStructuralFromFin_of_linear_count
    (![10, 4, 23] : Fin 3 → ZMod 29) (![6, 11, 14] : Fin 3 → ZMod 29)
  · decide
  · intro i
    apply (@Law1279.models_iff (ZMod 29) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation3345_not_termStructuralFromFin_Equation1279_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation3345_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_1,
Equation3345_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3345_not_termStructuralFromFin_Equation1279_linearCount

/-- A product of 3 distinct linear E1279 models over `ZMod 17` has too few
linear E3548 companions to admit term recovery. -/
theorem Equation3548_not_termStructuralFromFin_Equation1279_linearCount :
    ¬ Law3548.TermStructuralFromFin Law1279 := by
  apply not_termStructuralFromFin_of_linear_count
    (![5, 10, 6] : Fin 3 → ZMod 17) (![6, 8, 15] : Fin 3 → ZMod 17)
  · decide
  · intro i
    apply (@Law1279.models_iff (ZMod 17) (lin _ _)).mpr
    revert i
    native_decide
  · native_decide

/-- info: 'Equation3548_not_termStructuralFromFin_Equation1279_linearCount' depends on axioms: [propext, Classical.choice, Quot.sound,
Equation3548_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_1,
Equation3548_not_termStructuralFromFin_Equation1279_linearCount._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3548_not_termStructuralFromFin_Equation1279_linearCount
