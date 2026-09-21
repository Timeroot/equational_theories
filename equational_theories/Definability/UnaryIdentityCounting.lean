import equational_theories.Definability.StraightLineCounting

/-! The remaining short unary identities cannot recover all magmas by FO formulas.
The collision bounds are uniform in the cardinality, so compactness applies
only to unrestricted structural interpretation. -/

open Law Law.MagmaLaw
namespace UnaryIdentityCounting
open StraightLineCounting

def program99 : Program 3 where
  left := ![0, 1, 0]
  right := ![0, 0, 2]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture99 : Captures Law99 program99 := by
  intro G f hf x
  let a := f x x
  let b := f a x
  let c := f x b
  refine ⟨![x, a, b, c],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c] : Fin 4 → G) 3 = (![x, a, b, c] : Fin 4 → G) 0 := by
      exact ((@Law99.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program614 : Program 4 where
  left := ![0, 1, 0, 0]
  right := ![0, 0, 2, 3]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture614 : Captures Law614 program614 := by
  intro G f hf x
  let a := f x x
  let b := f a x
  let c := f x b
  let d := f x c
  refine ⟨![x, a, b, c, d],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c, d] : Fin 5 → G) 4 = (![x, a, b, c, d] : Fin 5 → G) 0 := by
      exact ((@Law614.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program817 : Program 3 where
  left := ![0, 1, 0]
  right := ![0, 1, 2]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture817 : Captures Law817 program817 := by
  intro G f hf x
  let a := f x x
  let b := f a a
  let c := f x b
  refine ⟨![x, a, b, c],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c] : Fin 4 → G) 3 = (![x, a, b, c] : Fin 4 → G) 0 := by
      exact ((@Law817.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program1020 : Program 4 where
  left := ![0, 0, 2, 0]
  right := ![0, 1, 0, 3]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture1020 : Captures Law1020 program1020 := by
  intro G f hf x
  let a := f x x
  let b := f x a
  let c := f b x
  let d := f x c
  refine ⟨![x, a, b, c, d],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c, d] : Fin 5 → G) 4 = (![x, a, b, c, d] : Fin 5 → G) 0 := by
      exact ((@Law1020.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program1223 : Program 4 where
  left := ![0, 1, 2, 0]
  right := ![0, 0, 0, 3]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture1223 : Captures Law1223 program1223 := by
  intro G f hf x
  let a := f x x
  let b := f a x
  let c := f b x
  let d := f x c
  refine ⟨![x, a, b, c, d],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c, d] : Fin 5 → G) 4 = (![x, a, b, c, d] : Fin 5 → G) 0 := by
      exact ((@Law1223.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program1426 : Program 3 where
  left := ![0, 0, 1]
  right := ![0, 1, 2]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture1426 : Captures Law1426 program1426 := by
  intro G f hf x
  let a := f x x
  let b := f x a
  let c := f a b
  refine ⟨![x, a, b, c],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c] : Fin 4 → G) 3 = (![x, a, b, c] : Fin 4 → G) 0 := by
      exact ((@Law1426.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program1629 : Program 3 where
  left := ![0, 1, 1]
  right := ![0, 0, 2]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture1629 : Captures Law1629 program1629 := by
  intro G f hf x
  let a := f x x
  let b := f a x
  let c := f a b
  refine ⟨![x, a, b, c],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c] : Fin 4 → G) 3 = (![x, a, b, c] : Fin 4 → G) 0 := by
      exact ((@Law1629.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program3456 : Program 3 where
  left := ![0, 1, 0]
  right := ![0, 0, 2]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture3456 : Captures Law3456 program3456 := by
  intro G f hf x
  let a := f x x
  let b := f a x
  let c := f x b
  refine ⟨![x, a, b, c],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c] : Fin 4 → G) 3 = (![x, a, b, c] : Fin 4 → G) 1 := by
      exact ((@Law3456.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

def program4380 : Program 3 where
  left := ![0, 0, 1]
  right := ![0, 1, 0]
  left_le := by decide
  right_le := by decide
  distinct := by decide

theorem capture4380 : Captures Law4380 program4380 := by
  intro G f hf x
  let a := f x x
  let b := f x a
  let c := f a x
  refine ⟨![x, a, b, c],rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro hi
    have he : (![x, a, b, c] : Fin 4 → G) 3 = (![x, a, b, c] : Fin 4 → G) 2 := by
      exact ((@Law4380.models_iff G ⟨f⟩).mp hf x).symm
    have hbad := congrArg Fin.val (hi he)
    norm_num at hbad

end UnaryIdentityCounting

theorem Equation99_not_StructuralFrom_Equation1_compactness :
    ¬ Law99.StructuralFrom Law1 :=
  StraightLineCounting.negative Law99 UnaryIdentityCounting.program99 UnaryIdentityCounting.capture99

/-- info: 'Equation99_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation1_compactness

theorem Equation614_not_StructuralFrom_Equation1_compactness :
    ¬ Law614.StructuralFrom Law1 :=
  StraightLineCounting.negative Law614 UnaryIdentityCounting.program614 UnaryIdentityCounting.capture614

/-- info: 'Equation614_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation1_compactness

theorem Equation817_not_StructuralFrom_Equation1_compactness :
    ¬ Law817.StructuralFrom Law1 :=
  StraightLineCounting.negative Law817 UnaryIdentityCounting.program817 UnaryIdentityCounting.capture817

/-- info: 'Equation817_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation1_compactness

theorem Equation1020_not_StructuralFrom_Equation1_compactness :
    ¬ Law1020.StructuralFrom Law1 :=
  StraightLineCounting.negative Law1020 UnaryIdentityCounting.program1020 UnaryIdentityCounting.capture1020

/-- info: 'Equation1020_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1020_not_StructuralFrom_Equation1_compactness

theorem Equation1223_not_StructuralFrom_Equation1_compactness :
    ¬ Law1223.StructuralFrom Law1 :=
  StraightLineCounting.negative Law1223 UnaryIdentityCounting.program1223 UnaryIdentityCounting.capture1223

/-- info: 'Equation1223_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation1_compactness

theorem Equation1426_not_StructuralFrom_Equation1_compactness :
    ¬ Law1426.StructuralFrom Law1 :=
  StraightLineCounting.negative Law1426 UnaryIdentityCounting.program1426 UnaryIdentityCounting.capture1426

/-- info: 'Equation1426_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation1_compactness

theorem Equation1629_not_StructuralFrom_Equation1_compactness :
    ¬ Law1629.StructuralFrom Law1 :=
  StraightLineCounting.negative Law1629 UnaryIdentityCounting.program1629 UnaryIdentityCounting.capture1629

/-- info: 'Equation1629_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1629_not_StructuralFrom_Equation1_compactness

theorem Equation3456_not_StructuralFrom_Equation1_compactness :
    ¬ Law3456.StructuralFrom Law1 :=
  StraightLineCounting.negative Law3456 UnaryIdentityCounting.program3456 UnaryIdentityCounting.capture3456

/-- info: 'Equation3456_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3456_not_StructuralFrom_Equation1_compactness

theorem Equation4380_not_StructuralFrom_Equation1_compactness :
    ¬ Law4380.StructuralFrom Law1 :=
  StraightLineCounting.negative Law4380 UnaryIdentityCounting.program4380 UnaryIdentityCounting.capture4380

/-- info: 'Equation4380_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation1_compactness
