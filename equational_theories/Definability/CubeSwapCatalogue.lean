import equational_theories.Definability.CubeOutputSwap

/-! Reversible first-order companions preserving squares and both cubes.
The recipes are defined for every magma; only the target-law proofs below
use a source equation. Each inverse is the uniform construction in
`CubeOutputSwap.recover`. -/

open Law Law.MagmaLaw CubeOutputSwap
namespace CubeSwapCatalogue
private theorem target_4439_3458 {G : Type} (M : Magma G) (h : @Equation4439 G M) :
    @Equation3458 G ((forward 2 6 false).magma M) := by
  classical
  intro x y
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation4439 at h
    grind

theorem Equation3458_structuralFrom_Equation4439_cubeSwap : Law3458.StructuralFrom Law4439 :=
  structuralFrom_cubeOutputSwap 2 6 false (fun M h =>
    (@Law3458.models_iff _ ((forward 2 6 false).magma M)).mpr (target_4439_3458 M ((@Law4439.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation3458_structuralFrom_Equation4439_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3458_structuralFrom_Equation4439_cubeSwap


private theorem target_138_3306 {G : Type} (M : Magma G) (h : @Equation138 G M) :
    @Equation3306 G ((forward 1 6 true).magma M) := by
  classical
  intro x y
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation138 at h
    grind

theorem Equation3306_structuralFrom_Equation138_cubeSwap : Law3306.StructuralFrom Law138 :=
  structuralFrom_cubeOutputSwap 1 6 true (fun M h =>
    (@Law3306.models_iff _ ((forward 1 6 true).magma M)).mpr (target_138_3306 M ((@Law138.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation3306_structuralFrom_Equation138_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3306_structuralFrom_Equation138_cubeSwap


private theorem target_4456_3458 {G : Type} (M : Magma G) (h : @Equation4456 G M) :
    @Equation3458 G ((forward 2 6 true).magma M) := by
  classical
  intro x y
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation4456 at h
    grind

theorem Equation3458_structuralFrom_Equation4456_cubeSwap : Law3458.StructuralFrom Law4456 :=
  structuralFrom_cubeOutputSwap 2 6 true (fun M h =>
    (@Law3458.models_iff _ ((forward 2 6 true).magma M)).mpr (target_4456_3458 M ((@Law4456.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation3458_structuralFrom_Equation4456_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3458_structuralFrom_Equation4456_cubeSwap


private theorem target_101_1223 {G : Type} (M : Magma G) (h : @Equation101 G M) :
    @Equation1223 G ((forward 3 9 true).magma M) := by
  classical
  intro x
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation101 at h
    grind

theorem Equation1223_structuralFrom_Equation101_cubeSwap : Law1223.StructuralFrom Law101 :=
  structuralFrom_cubeOutputSwap 3 9 true (fun M h =>
    (@Law1223.models_iff _ ((forward 3 9 true).magma M)).mpr (target_101_1223 M ((@Law101.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation1223_structuralFrom_Equation101_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_structuralFrom_Equation101_cubeSwap


private theorem target_4434_3457 {G : Type} (M : Magma G) (h : @Equation4434 G M) :
    @Equation3457 G ((forward 2 6 false).magma M) := by
  classical
  intro x y
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation4434 at h
    grind

theorem Equation3457_structuralFrom_Equation4434_cubeSwap : Law3457.StructuralFrom Law4434 :=
  structuralFrom_cubeOutputSwap 2 6 false (fun M h =>
    (@Law3457.models_iff _ ((forward 2 6 false).magma M)).mpr (target_4434_3457 M ((@Law4434.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation3457_structuralFrom_Equation4434_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3457_structuralFrom_Equation4434_cubeSwap


private theorem target_4456_3461 {G : Type} (M : Magma G) (h : @Equation4456 G M) :
    @Equation3461 G ((forward 2 6 false).magma M) := by
  classical
  intro x y
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation4456 at h
    grind

theorem Equation3461_structuralFrom_Equation4456_cubeSwap : Law3461.StructuralFrom Law4456 :=
  structuralFrom_cubeOutputSwap 2 6 false (fun M h =>
    (@Law3461.models_iff _ ((forward 2 6 false).magma M)).mpr (target_4456_3461 M ((@Law4456.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation3461_structuralFrom_Equation4456_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3461_structuralFrom_Equation4456_cubeSwap


private theorem target_4490_3461 {G : Type} (M : Magma G) (h : @Equation4490 G M) :
    @Equation3461 G ((forward 2 6 false).magma M) := by
  classical
  intro x y
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation4490 at h
    grind

theorem Equation3461_structuralFrom_Equation4490_cubeSwap : Law3461.StructuralFrom Law4490 :=
  structuralFrom_cubeOutputSwap 2 6 false (fun M h =>
    (@Law3461.models_iff _ ((forward 2 6 false).magma M)).mpr (target_4490_3461 M ((@Law4490.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation3461_structuralFrom_Equation4490_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3461_structuralFrom_Equation4490_cubeSwap


private theorem target_168_1629 {G : Type} (M : Magma G) (h : @Equation168 G M) :
    @Equation1629 G ((forward 0 0 true).magma M) := by
  classical
  have square_square (x : G) : M.op (M.op x x) (M.op x x) = x := (h x x x).symm
  have cube_square (x : G) : M.op (M.op (M.op x x) x) (M.op x x) = x :=
    (h x (M.op x x) x).symm
  intro x
  simp only [square, left_cube]
  rw [forward_apply]
  simp only [if_true, Equiv.swap_self, Equiv.refl_apply]
  split_ifs with hf
  · unfold fixedEntry at hf
    grind
  · exact (cube_square x).symm

theorem Equation1629_structuralFrom_Equation168_cubeSwap : Law1629.StructuralFrom Law168 :=
  structuralFrom_cubeOutputSwap 0 0 true (fun M h =>
    (@Law1629.models_iff _ ((forward 0 0 true).magma M)).mpr (target_168_1629 M ((@Law168.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation1629_structuralFrom_Equation168_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1629_structuralFrom_Equation168_cubeSwap


private theorem target_1489_99 {G : Type} (M : Magma G) (h : @Equation1489 G M) :
    @Equation99 G ((forward 1 6 true).magma M) := by
  classical
  intro x
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation1489 at h
    grind

theorem Equation99_structuralFrom_Equation1489_cubeSwap : Law99.StructuralFrom Law1489 :=
  structuralFrom_cubeOutputSwap 1 6 true (fun M h =>
    (@Law99.models_iff _ ((forward 1 6 true).magma M)).mpr (target_1489_99 M ((@Law1489.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation99_structuralFrom_Equation1489_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_structuralFrom_Equation1489_cubeSwap


private theorem target_1042_1223 {G : Type} (M : Magma G) (h : @Equation1042 G M) :
    @Equation1223 G ((forward 3 9 true).magma M) := by
  classical
  intro x
  simp [forward_apply, fixedEntry, value, Equiv.swap_apply_def]
  all_goals
    unfold Equation1042 at h
    grind

theorem Equation1223_structuralFrom_Equation1042_cubeSwap : Law1223.StructuralFrom Law1042 :=
  structuralFrom_cubeOutputSwap 3 9 true (fun M h =>
    (@Law1223.models_iff _ ((forward 3 9 true).magma M)).mpr (target_1042_1223 M ((@Law1042.models_iff _ M).mp h)))

/-- info: 'CubeSwapCatalogue.Equation1223_structuralFrom_Equation1042_cubeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_structuralFrom_Equation1042_cubeSwap

end CubeSwapCatalogue
