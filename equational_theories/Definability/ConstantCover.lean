import equational_theories.Definability.Constant

/-!
# A cover of the constant-magma refutations

The constant magma on `Fin 2` models every law whose two sides are both compound, and its clone is
just `{π₁, π₂, const}`. `Law1519` `x = (y ◇ y) ◇ (x ◇ (y ◇ y))` holds for none of the three, so it is not
term-definable from any of them. These are the 14 such pairs the rest of the development
leaves open; the dual pairs, against `Law2128`, follow by symmetry.

This file is generated.
-/

open Law Law.MagmaLaw

theorem const_refutes_1519_fst : ¬ @Equation1519 (Fin 2) ⟨fun x _ ↦ x⟩ := by decide

theorem const_refutes_1519_snd : ¬ @Equation1519 (Fin 2) ⟨fun _ y ↦ y⟩ := by decide

theorem const_refutes_1519_const : ¬ @Equation1519 (Fin 2) (Magma.const (0 : Fin 2)) := by decide

/-- `x ◇ x = y ◇ y` -/
theorem const_satisfies_40 : @Equation40 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ x = y ◇ (x ◇ y)` -/
theorem const_satisfies_313 : @Equation313 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ x = y ◇ (x ◇ (y ◇ y))` -/
theorem const_satisfies_3272 : @Equation3272 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ y = y ◇ (z ◇ (x ◇ z))` -/
theorem const_satisfies_3364 : @Equation3364 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ x = y ◇ ((x ◇ x) ◇ y)` -/
theorem const_satisfies_3472 : @Equation3472 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ y = z ◇ ((x ◇ y) ◇ z)` -/
theorem const_satisfies_3588 : @Equation3588 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ y = z ◇ ((z ◇ y) ◇ x)` -/
theorem const_satisfies_3620 : @Equation3620 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ x = (y ◇ x) ◇ (y ◇ y)` -/
theorem const_satisfies_3678 : @Equation3678 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ (x ◇ x) = y ◇ (x ◇ y)` -/
theorem const_satisfies_4273 : @Equation4273 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ (x ◇ y) = z ◇ (y ◇ z)` -/
theorem const_satisfies_4305 : @Equation4305 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ (x ◇ x) = (y ◇ x) ◇ y` -/
theorem const_satisfies_4386 : @Equation4386 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ (x ◇ y) = (y ◇ z) ◇ z` -/
theorem const_satisfies_4413 : @Equation4413 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ (x ◇ y) = (z ◇ x) ◇ x` -/
theorem const_satisfies_4415 : @Equation4415 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

/-- `x ◇ (x ◇ y) = (z ◇ y) ◇ z` -/
theorem const_satisfies_4421 : @Equation4421 (Fin 2) (Magma.const (0 : Fin 2)) := by
  decide

theorem Equation1519_not_termDefinableFrom_Equation40 :
    ¬ Law1519.TermDefinableFrom Law40 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law40.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_40)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation313 :
    ¬ Law1519.TermDefinableFrom Law313 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law313.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_313)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation3272 :
    ¬ Law1519.TermDefinableFrom Law3272 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law3272.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_3272)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation3364 :
    ¬ Law1519.TermDefinableFrom Law3364 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law3364.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_3364)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation3472 :
    ¬ Law1519.TermDefinableFrom Law3472 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law3472.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_3472)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation3588 :
    ¬ Law1519.TermDefinableFrom Law3588 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law3588.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_3588)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation3620 :
    ¬ Law1519.TermDefinableFrom Law3620 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law3620.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_3620)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation3678 :
    ¬ Law1519.TermDefinableFrom Law3678 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law3678.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_3678)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation4273 :
    ¬ Law1519.TermDefinableFrom Law4273 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law4273.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_4273)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation4305 :
    ¬ Law1519.TermDefinableFrom Law4305 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law4305.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_4305)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation4386 :
    ¬ Law1519.TermDefinableFrom Law4386 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law4386.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_4386)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation4413 :
    ¬ Law1519.TermDefinableFrom Law4413 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law4413.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_4413)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation4415 :
    ¬ Law1519.TermDefinableFrom Law4415 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law4415.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_4415)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))

theorem Equation1519_not_termDefinableFrom_Equation4421 :
    ¬ Law1519.TermDefinableFrom Law4421 :=
  not_termDefinableFrom_of_const (0 : Fin 2)
    ((@Law4421.models_iff (Fin 2) (Magma.const 0)).mpr const_satisfies_4421)
    (fun h ↦ const_refutes_1519_fst ((@Law1519.models_iff (Fin 2) ⟨fun x _ ↦ x⟩).mp h))
    (fun h ↦ const_refutes_1519_snd ((@Law1519.models_iff (Fin 2) ⟨fun _ y ↦ y⟩).mp h))
    (fun h ↦ const_refutes_1519_const ((@Law1519.models_iff (Fin 2) (Magma.const 0)).mp h))
