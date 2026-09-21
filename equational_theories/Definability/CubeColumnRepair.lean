import equational_theories.Definability.Reversible

/-! A reversible, quantifier-free interpretation from E3471 to E108.
Write s(y)=y*y and c(y)=(y*y)*y. E3471 makes the columns c(y) constant
with value s(y), and every s(y) is a right-zero idempotent. In nonfixed
columns a three-cycle of input positions records c(y) on the new diagonal
and s(y) in the new right cube. Fixed columns become right identities.
The inverse reads both old unary maps from these two new unary terms. -/

open FreeMagma Law Law.MagmaLaw
namespace CubeColumnRepair

private abbrev x : FreeMagma (Fin 2) := .Leaf 0
private abbrev y : FreeMagma (Fin 2) := .Leaf 1
private abbrev s : FreeMagma (Fin 2) := y ⋆ y
private abbrev c : FreeMagma (Fin 2) := s ⋆ y

def forward : QFOp :=
  .ite y s (.leaf x)
    (.ite c s (.leaf (x ⋆ y))
      (.ite x y (.leaf c)
        (.ite x c (.leaf s)
          (.ite x s (.leaf (c ⋆ y)) (.leaf (x ⋆ y))))))

def backward : QFOp :=
  .ite y c (.leaf y)
    (.ite s c (.leaf (x ⋆ y))
      (.ite x y (.leaf c)
        (.ite x c (.leaf s)
          (.ite x s (.leaf (c ⋆ y)) (.leaf (x ⋆ y))))))

open scoped Classical in
theorem forward_apply {G : Type} (M : Magma G) (a b : G) :
    (forward.magma M).op a b =
      if b = M.op b b then a
      else if M.op (M.op b b) b = M.op b b then M.op a b
      else if a = b then M.op (M.op b b) b
      else if a = M.op (M.op b b) b then M.op b b
      else if a = M.op b b then M.op (M.op (M.op b b) b) b
      else M.op a b := rfl

open scoped Classical in
theorem backward_apply {G : Type} (M : Magma G) (a b : G) :
    (backward.magma M).op a b =
      if b = M.op (M.op b b) b then b
      else if M.op b b = M.op (M.op b b) b then M.op a b
      else if a = b then M.op (M.op b b) b
      else if a = M.op (M.op b b) b then M.op b b
      else if a = M.op b b then M.op (M.op (M.op b b) b) b
      else M.op a b := rfl

structure Suitable {G : Type} (M : Magma G) : Prop where
  square_column (a b : G) : M.op b (M.op a a) = M.op a a
  cube_fixed (a : G) : M.op (M.op a a) a = a → M.op a a = a

variable {G : Type} (M : Magma G) (h : Suitable M)
include h

theorem square_column (a b : G) : M.op b (M.op a a) = M.op a a :=
  h.square_column a b

theorem square_idempotent (a : G) : M.op (M.op a a) (M.op a a) = M.op a a :=
  square_column M h a _

theorem cube_ne_self (a : G) (ha : a ≠ M.op a a) : M.op (M.op a a) a ≠ a :=
  fun he => ha (h.cube_fixed a he).symm

omit h in
theorem forward_square (a : G) : (forward.magma M).op a a = M.op (M.op a a) a := by
  classical
  rw [forward_apply]
  split_ifs <;> grind

theorem forward_cube (a : G) :
    (forward.magma M).op ((forward.magma M).op a a) a = M.op a a := by
  classical
  rw [forward_square M, forward_apply]
  by_cases ha : a = M.op a a
  · have haa : M.op a a = a := ha.symm
    simp only [haa, ↓reduceIte]
  · have hc := cube_ne_self M h a ha
    simp only [ha, ↓reduceIte, hc]
    split_ifs with hs
    · rw [hs]
      exact hs
    · rfl

theorem forward_fixed_column (a b : G) :
    (forward.magma M).op b (M.op a a) = b := by
  classical
  rw [forward_apply, square_idempotent M h]
  simp

theorem target : @Equation108 G (forward.magma M) := by
  intro x y
  rw [forward_cube M h, forward_fixed_column M h]

theorem recover : backward.magma (forward.magma M) = M := by
  classical
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext a b
  change (backward.magma (forward.magma M)).op a b = M.op a b
  rw [backward_apply, forward_cube M h, forward_square M]
  by_cases hb : b = M.op b b
  · rw [if_pos hb]
    rw [hb, square_column M h]
  · rw [if_neg hb]
    by_cases hc : M.op (M.op b b) b = M.op b b
    · rw [if_pos hc, forward_apply, if_neg hb, if_pos hc]
    · rw [if_neg hc]
      have hcb := cube_ne_self M h b hb
      split_ifs with hab has hac
      · subst a
        rfl
      · rw [has]
      · rw [hac, forward_apply, if_neg hb, if_neg hc, if_neg (Ne.symm hb),
          if_neg (Ne.symm hc), if_pos rfl]
      · rw [forward_apply, if_neg hb, if_neg hc, if_neg hab, if_neg hac, if_neg has]

omit h
theorem suitable3471 (M : Magma G) (h : @Equation3471 G M) : Suitable M := by
  constructor
  · intro a b
    let c := M.op (M.op a a) a
    have hc (z : G) : M.op z c = M.op a a := (h a z).symm
    have hcc : M.op c c = M.op a a := hc c
    have hccc : M.op (M.op c c) c = M.op a a := by rw [hcc, hc]
    have hh := h c b
    rw [hccc, hcc] at hh
    exact hh.symm
  · intro a he
    have hc := h a (M.op a a)
    rw [he, he] at hc
    exact hc

theorem suitable317 (M : Magma G) (h : @Equation317 G M) : Suitable M := by
  constructor
  · intro a b
    have hh : M.op a a = M.op b b := (h a b b).trans (h b b b).symm
    rw [hh]
    exact (h b b b).symm
  · intro a he
    have hh := h a (M.op a a) a
    rw [he, he] at hh
    exact hh

theorem suitable3283 (M : Magma G) (h : @Equation3283 G M) : Suitable M := by
  constructor
  · intro a b
    have hh : M.op a a = M.op b b := (h a b b).trans (h b b b).symm
    have hb := h b b b
    have hb' := h b b (M.op b b)
    have hh' : M.op b (M.op b (M.op b b)) = M.op b b := hb.symm
    rw [hh'] at hb'
    rw [hh]
    exact hb'.symm
  · intro a he
    have hh := h a (M.op a a) a
    rw [he, he, he] at hh
    exact hh

theorem suitable3270 (M : Magma G) (h : @Equation3270 G M) : Suitable M := by
  constructor
  · intro a b
    have h1 := h a b (M.op a a)
    have h2 := h a a a
    rw [← h2] at h1
    exact h1.symm
  · intro a he
    grind

theorem suitable3280 (M : Magma G) (h : @Equation3280 G M) : Suitable M := by
  constructor
  · intro a b
    grind
  · intro a he
    grind

end CubeColumnRepair

open Law Law.MagmaLaw

theorem Equation108_StructuralFrom_Equation3471_cubeColumn : Law108.StructuralFrom Law3471 :=
  structuralFrom_of_qfInverse CubeColumnRepair.forward CubeColumnRepair.backward
    (fun M h => CubeColumnRepair.recover M (CubeColumnRepair.suitable3471 M ((@Law3471.models_iff _ M).mp h)))
    (fun M h => (@Law108.models_iff _ (CubeColumnRepair.forward.magma M)).mpr
      (CubeColumnRepair.target M (CubeColumnRepair.suitable3471 M ((@Law3471.models_iff _ M).mp h))))

/-- info: 'Equation108_StructuralFrom_Equation3471_cubeColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_StructuralFrom_Equation3471_cubeColumn


theorem Equation108_StructuralFrom_Equation317_cubeColumn : Law108.StructuralFrom Law317 :=
  structuralFrom_of_qfInverse CubeColumnRepair.forward CubeColumnRepair.backward
    (fun M h => CubeColumnRepair.recover M (CubeColumnRepair.suitable317 M ((@Law317.models_iff _ M).mp h)))
    (fun M h => (@Law108.models_iff _ (CubeColumnRepair.forward.magma M)).mpr
      (CubeColumnRepair.target M (CubeColumnRepair.suitable317 M ((@Law317.models_iff _ M).mp h))))

/-- info: 'Equation108_StructuralFrom_Equation317_cubeColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_StructuralFrom_Equation317_cubeColumn


theorem Equation108_StructuralFrom_Equation3283_cubeColumn : Law108.StructuralFrom Law3283 :=
  structuralFrom_of_qfInverse CubeColumnRepair.forward CubeColumnRepair.backward
    (fun M h => CubeColumnRepair.recover M (CubeColumnRepair.suitable3283 M ((@Law3283.models_iff _ M).mp h)))
    (fun M h => (@Law108.models_iff _ (CubeColumnRepair.forward.magma M)).mpr
      (CubeColumnRepair.target M (CubeColumnRepair.suitable3283 M ((@Law3283.models_iff _ M).mp h))))

/-- info: 'Equation108_StructuralFrom_Equation3283_cubeColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_StructuralFrom_Equation3283_cubeColumn


theorem Equation108_StructuralFrom_Equation3270_cubeColumn : Law108.StructuralFrom Law3270 :=
  structuralFrom_of_qfInverse CubeColumnRepair.forward CubeColumnRepair.backward
    (fun M h => CubeColumnRepair.recover M (CubeColumnRepair.suitable3270 M ((@Law3270.models_iff _ M).mp h)))
    (fun M h => (@Law108.models_iff _ (CubeColumnRepair.forward.magma M)).mpr
      (CubeColumnRepair.target M (CubeColumnRepair.suitable3270 M ((@Law3270.models_iff _ M).mp h))))

/-- info: 'Equation108_StructuralFrom_Equation3270_cubeColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_StructuralFrom_Equation3270_cubeColumn


theorem Equation108_StructuralFrom_Equation3280_cubeColumn : Law108.StructuralFrom Law3280 :=
  structuralFrom_of_qfInverse CubeColumnRepair.forward CubeColumnRepair.backward
    (fun M h => CubeColumnRepair.recover M (CubeColumnRepair.suitable3280 M ((@Law3280.models_iff _ M).mp h)))
    (fun M h => (@Law108.models_iff _ (CubeColumnRepair.forward.magma M)).mpr
      (CubeColumnRepair.target M (CubeColumnRepair.suitable3280 M ((@Law3280.models_iff _ M).mp h))))

/-- info: 'Equation108_StructuralFrom_Equation3280_cubeColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_StructuralFrom_Equation3280_cubeColumn
