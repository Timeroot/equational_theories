import equational_theories.Definability.ConstantTermBlockCountsC2
import equational_theories.Definability.ConstantTermBlockCountsC3
import equational_theories.Definability.ConstantTermBlockCountsC4
import equational_theories.Definability.ConstantTermBlockCountsV4
import equational_theories.Definability.PointedIdentityCountsC5

/-! Unrestricted FO-structural negatives from constant unary terms and
five-point local groups. The amplification to arbitrarily many blocks
uses compactness; these are not finite FO-structural counterexamples. -/

open Law Law.MagmaLaw

local instance : Fact (1 < 4) := ⟨by decide⟩
local instance : Fact (1 < 5) := ⟨by decide⟩

theorem Equation3256_not_StructuralFrom_Equation40_constantBlocksC2 :
    ¬ Law3256.StructuralFrom Law40 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left40) (t := ConstantTermBlockCounting.C2.right40)
    (by rw [ConstantTermBlockCounting.C2.target3256]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3256, ConstantTermBlockCounting.C2.source40]; decide)

/-- info: 'Equation3256_not_StructuralFrom_Equation40_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3256_not_StructuralFrom_Equation40_constantBlocksC2

theorem Equation108_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law108.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target108]; decide)
    (by rw [PointedIdentityCounting.C2.target108, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation108_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation630_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law630.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target630]; decide)
    (by rw [PointedIdentityCounting.C2.target630, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation630_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation630_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation643_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law643.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target643]; decide)
    (by rw [PointedIdentityCounting.C2.target643, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation643_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation643_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation818_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law818.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target818]; decide)
    (by rw [PointedIdentityCounting.C2.target818, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation818_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation818_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation843_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law843.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target843]; decide)
    (by rw [PointedIdentityCounting.C2.target843, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation843_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation843_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation1224_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law1224.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target1224]; decide)
    (by rw [PointedIdentityCounting.C2.target1224, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation1224_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1224_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation1249_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law1249.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target1249]; decide)
    (by rw [PointedIdentityCounting.C2.target1249, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation1249_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1249_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation1515_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law1515.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target1515]; decide)
    (by rw [PointedIdentityCounting.C2.target1515, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation1515_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1515_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation1519_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law1519.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [ConstantTermBlockCounting.C2.target1519]; decide)
    (by rw [ConstantTermBlockCounting.C2.target1519, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation1519_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1519_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation3465_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law3465.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target3465]; decide)
    (by rw [PointedIdentityCounting.C2.target3465, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation3465_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3465_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation3484_not_StructuralFrom_Equation316_constantBlocksC2 :
    ¬ Law3484.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left316) (t := ConstantTermBlockCounting.C2.right316)
    (by rw [PointedIdentityCounting.C2.target3484]; decide)
    (by rw [PointedIdentityCounting.C2.target3484, ConstantTermBlockCounting.C2.source316]; decide)

/-- info: 'Equation3484_not_StructuralFrom_Equation316_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3484_not_StructuralFrom_Equation316_constantBlocksC2

theorem Equation3472_not_StructuralFrom_Equation3282_constantBlocksC2 :
    ¬ Law3472.StructuralFrom Law3282 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3282) (t := ConstantTermBlockCounting.C2.right3282)
    (by rw [ConstantTermBlockCounting.C2.target3472]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3472, ConstantTermBlockCounting.C2.source3282]; decide)

/-- info: 'Equation3472_not_StructuralFrom_Equation3282_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3472_not_StructuralFrom_Equation3282_constantBlocksC2

theorem Equation4276_not_StructuralFrom_Equation3282_constantBlocksC2 :
    ¬ Law4276.StructuralFrom Law3282 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3282) (t := ConstantTermBlockCounting.C2.right3282)
    (by rw [ConstantTermBlockCounting.C2.target4276]; decide)
    (by rw [ConstantTermBlockCounting.C2.target4276, ConstantTermBlockCounting.C2.source3282]; decide)

/-- info: 'Equation4276_not_StructuralFrom_Equation3282_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4276_not_StructuralFrom_Equation3282_constantBlocksC2

theorem Equation414_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law414.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target414]; decide)
    (by rw [ConstantTermBlockCounting.C2.target414, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation414_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation414_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation820_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law820.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target820]; decide)
    (by rw [ConstantTermBlockCounting.C2.target820, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation820_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation820_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation823_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law823.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target823]; decide)
    (by rw [ConstantTermBlockCounting.C2.target823, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation823_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation823_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation846_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law846.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target846]; decide)
    (by rw [ConstantTermBlockCounting.C2.target846, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation846_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation846_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation1036_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law1036.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target1036]; decide)
    (by rw [ConstantTermBlockCounting.C2.target1036, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation1036_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1036_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation1049_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law1049.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target1049]; decide)
    (by rw [ConstantTermBlockCounting.C2.target1049, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation1049_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1049_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation3262_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law3262.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target3262]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3262, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation3262_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3262_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation3268_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law3268.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target3268]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3268, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation3268_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3268_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation3272_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law3272.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target3272]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3272, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation3272_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3272_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation3660_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law3660.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target3660]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3660, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation3660_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3660_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation3668_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law3668.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target3668]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3668, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation3668_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3668_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation3678_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law3678.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target3678]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3678, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation3678_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3678_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation4343_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law4343.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target4343]; decide)
    (by rw [ConstantTermBlockCounting.C2.target4343, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation4343_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4343_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation4388_not_StructuralFrom_Equation3485_constantBlocksC2 :
    ¬ Law4388.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left3485) (t := ConstantTermBlockCounting.C2.right3485)
    (by rw [ConstantTermBlockCounting.C2.target4388]; decide)
    (by rw [ConstantTermBlockCounting.C2.target4388, ConstantTermBlockCounting.C2.source3485]; decide)

/-- info: 'Equation4388_not_StructuralFrom_Equation3485_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4388_not_StructuralFrom_Equation3485_constantBlocksC2

theorem Equation108_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law108.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target108]; decide)
    (by rw [PointedIdentityCounting.C2.target108, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation108_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation630_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law630.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target630]; decide)
    (by rw [PointedIdentityCounting.C2.target630, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation630_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation630_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation643_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law643.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target643]; decide)
    (by rw [PointedIdentityCounting.C2.target643, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation643_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation643_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation818_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law818.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target818]; decide)
    (by rw [PointedIdentityCounting.C2.target818, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation818_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation818_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation819_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law819.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target819]; decide)
    (by rw [ConstantTermBlockCounting.C2.target819, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation819_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation819_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation843_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law843.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target843]; decide)
    (by rw [PointedIdentityCounting.C2.target843, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation843_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation843_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation845_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law845.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target845]; decide)
    (by rw [ConstantTermBlockCounting.C2.target845, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation845_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation845_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation846_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law846.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target846]; decide)
    (by rw [ConstantTermBlockCounting.C2.target846, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation846_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation846_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation1049_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law1049.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target1049]; decide)
    (by rw [ConstantTermBlockCounting.C2.target1049, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation1049_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1049_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation1224_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law1224.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target1224]; decide)
    (by rw [PointedIdentityCounting.C2.target1224, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation1224_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1224_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation1249_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law1249.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target1249]; decide)
    (by rw [PointedIdentityCounting.C2.target1249, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation1249_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1249_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation1252_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law1252.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target1252]; decide)
    (by rw [ConstantTermBlockCounting.C2.target1252, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation1252_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1252_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation1515_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law1515.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target1515]; decide)
    (by rw [PointedIdentityCounting.C2.target1515, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation1515_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1515_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation1519_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law1519.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target1519]; decide)
    (by rw [ConstantTermBlockCounting.C2.target1519, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation1519_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1519_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3268_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law3268.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target3268]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3268, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation3268_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3268_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3272_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law3272.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target3272]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3272, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation3272_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3272_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3457_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law3457.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target3457]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3457, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation3457_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3457_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3465_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law3465.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target3465]; decide)
    (by rw [PointedIdentityCounting.C2.target3465, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation3465_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3465_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3484_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law3484.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [PointedIdentityCounting.C2.target3484]; decide)
    (by rw [PointedIdentityCounting.C2.target3484, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation3484_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3484_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3678_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law3678.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target3678]; decide)
    (by rw [ConstantTermBlockCounting.C2.target3678, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation3678_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3678_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation4388_not_StructuralFrom_Equation4389_constantBlocksC2 :
    ¬ Law4388.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C2.H) (s := ConstantTermBlockCounting.C2.left4389) (t := ConstantTermBlockCounting.C2.right4389)
    (by rw [ConstantTermBlockCounting.C2.target4388]; decide)
    (by rw [ConstantTermBlockCounting.C2.target4388, ConstantTermBlockCounting.C2.source4389]; decide)

/-- info: 'Equation4388_not_StructuralFrom_Equation4389_constantBlocksC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4388_not_StructuralFrom_Equation4389_constantBlocksC2

theorem Equation3278_not_StructuralFrom_Equation40_constantBlocksC3 :
    ¬ Law3278.StructuralFrom Law40 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left40) (t := ConstantTermBlockCounting.C3.right40)
    (by rw [ConstantTermBlockCounting.C3.target3278]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3278, ConstantTermBlockCounting.C3.source40]; decide)

theorem Equation107_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law107.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target107]; decide)
    (by rw [PointedIdentityCounting.C3.target107, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation819_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law819.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target819]; decide)
    (by rw [PointedIdentityCounting.C3.target819, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation825_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law825.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target825]; decide)
    (by rw [PointedIdentityCounting.C3.target825, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation845_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law845.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target845]; decide)
    (by rw [PointedIdentityCounting.C3.target845, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation1225_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law1225.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target1225]; decide)
    (by rw [PointedIdentityCounting.C3.target1225, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation1251_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law1251.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target1251]; decide)
    (by rw [PointedIdentityCounting.C3.target1251, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation1252_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law1252.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target1252]; decide)
    (by rw [PointedIdentityCounting.C3.target1252, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation1429_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law1429.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target1429]; decide)
    (by rw [PointedIdentityCounting.C3.target1429, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation3457_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law3457.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [PointedIdentityCounting.C3.target3457]; decide)
    (by rw [PointedIdentityCounting.C3.target3457, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation3667_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law3667.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [ConstantTermBlockCounting.C3.target3667]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3667, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation4389_not_StructuralFrom_Equation316_constantBlocksC3 :
    ¬ Law4389.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left316) (t := ConstantTermBlockCounting.C3.right316)
    (by rw [ConstantTermBlockCounting.C3.target4389]; decide)
    (by rw [ConstantTermBlockCounting.C3.target4389, ConstantTermBlockCounting.C3.source316]; decide)

theorem Equation1028_not_StructuralFrom_Equation3282_constantBlocksC3 :
    ¬ Law1028.StructuralFrom Law3282 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3282) (t := ConstantTermBlockCounting.C3.right3282)
    (by rw [ConstantTermBlockCounting.C3.target1028]; decide)
    (by rw [ConstantTermBlockCounting.C3.target1028, ConstantTermBlockCounting.C3.source3282]; decide)

theorem Equation3464_not_StructuralFrom_Equation3282_constantBlocksC3 :
    ¬ Law3464.StructuralFrom Law3282 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3282) (t := ConstantTermBlockCounting.C3.right3282)
    (by rw [ConstantTermBlockCounting.C3.target3464]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3464, ConstantTermBlockCounting.C3.source3282]; decide)

theorem Equation436_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law436.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [ConstantTermBlockCounting.C3.target436]; decide)
    (by rw [ConstantTermBlockCounting.C3.target436, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation835_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law835.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [PointedIdentityCounting.C3.target835]; decide)
    (by rw [PointedIdentityCounting.C3.target835, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation842_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law842.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [PointedIdentityCounting.C3.target842]; decide)
    (by rw [PointedIdentityCounting.C3.target842, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation1248_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law1248.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [ConstantTermBlockCounting.C3.target1248]; decide)
    (by rw [ConstantTermBlockCounting.C3.target1248, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation1637_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law1637.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [PointedIdentityCounting.C3.target1637]; decide)
    (by rw [PointedIdentityCounting.C3.target1637, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation1731_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law1731.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [PointedIdentityCounting.C3.target1731]; decide)
    (by rw [PointedIdentityCounting.C3.target1731, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation3258_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law3258.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [ConstantTermBlockCounting.C3.target3258]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3258, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation3661_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law3661.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [PointedIdentityCounting.C3.target3661]; decide)
    (by rw [PointedIdentityCounting.C3.target3661, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation3712_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law3712.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [ConstantTermBlockCounting.C3.target3712]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3712, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation3721_not_StructuralFrom_Equation3485_constantBlocksC3 :
    ¬ Law3721.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left3485) (t := ConstantTermBlockCounting.C3.right3485)
    (by rw [ConstantTermBlockCounting.C3.target3721]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3721, ConstantTermBlockCounting.C3.source3485]; decide)

theorem Equation1637_not_StructuralFrom_Equation4276_constantBlocksC3 :
    ¬ Law1637.StructuralFrom Law4276 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left4276) (t := ConstantTermBlockCounting.C3.right4276)
    (by rw [PointedIdentityCounting.C3.target1637]; decide)
    (by rw [PointedIdentityCounting.C3.target1637, ConstantTermBlockCounting.C3.source4276]; decide)

theorem Equation1731_not_StructuralFrom_Equation4276_constantBlocksC3 :
    ¬ Law1731.StructuralFrom Law4276 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left4276) (t := ConstantTermBlockCounting.C3.right4276)
    (by rw [PointedIdentityCounting.C3.target1731]; decide)
    (by rw [PointedIdentityCounting.C3.target1731, ConstantTermBlockCounting.C3.source4276]; decide)

theorem Equation825_not_StructuralFrom_Equation4389_constantBlocksC3 :
    ¬ Law825.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left4389) (t := ConstantTermBlockCounting.C3.right4389)
    (by rw [PointedIdentityCounting.C3.target825]; decide)
    (by rw [PointedIdentityCounting.C3.target825, ConstantTermBlockCounting.C3.source4389]; decide)

theorem Equation1251_not_StructuralFrom_Equation4389_constantBlocksC3 :
    ¬ Law1251.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left4389) (t := ConstantTermBlockCounting.C3.right4389)
    (by rw [PointedIdentityCounting.C3.target1251]; decide)
    (by rw [PointedIdentityCounting.C3.target1251, ConstantTermBlockCounting.C3.source4389]; decide)

theorem Equation3667_not_StructuralFrom_Equation4389_constantBlocksC3 :
    ¬ Law3667.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C3.H) (s := ConstantTermBlockCounting.C3.left4389) (t := ConstantTermBlockCounting.C3.right4389)
    (by rw [ConstantTermBlockCounting.C3.target3667]; decide)
    (by rw [ConstantTermBlockCounting.C3.target3667, ConstantTermBlockCounting.C3.source4389]; decide)

theorem Equation622_not_StructuralFrom_Equation316_constantBlocksC4 :
    ¬ Law622.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left316) (t := ConstantTermBlockCounting.C4.right316)
    (by rw [PointedIdentityCounting.C4.target622]; decide)
    (by rw [PointedIdentityCounting.C4.target622, ConstantTermBlockCounting.C4.source316]; decide)

theorem Equation1226_not_StructuralFrom_Equation316_constantBlocksC4 :
    ¬ Law1226.StructuralFrom Law316 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left316) (t := ConstantTermBlockCounting.C4.right316)
    (by rw [PointedIdentityCounting.C4.target1226]; decide)
    (by rw [PointedIdentityCounting.C4.target1226, ConstantTermBlockCounting.C4.source316]; decide)

theorem Equation3315_not_StructuralFrom_Equation3485_constantBlocksC4 :
    ¬ Law3315.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left3485) (t := ConstantTermBlockCounting.C4.right3485)
    (by rw [PointedIdentityCounting.C4.target3315]; decide)
    (by rw [PointedIdentityCounting.C4.target3315, ConstantTermBlockCounting.C4.source3485]; decide)

theorem Equation3509_not_StructuralFrom_Equation3485_constantBlocksC4 :
    ¬ Law3509.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left3485) (t := ConstantTermBlockCounting.C4.right3485)
    (by rw [ConstantTermBlockCounting.C4.target3509]; decide)
    (by rw [ConstantTermBlockCounting.C4.target3509, ConstantTermBlockCounting.C4.source3485]; decide)

theorem Equation4482_not_StructuralFrom_Equation3485_constantBlocksC4 :
    ¬ Law4482.StructuralFrom Law3485 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left3485) (t := ConstantTermBlockCounting.C4.right3485)
    (by rw [ConstantTermBlockCounting.C4.target4482]; decide)
    (by rw [ConstantTermBlockCounting.C4.target4482, ConstantTermBlockCounting.C4.source3485]; decide)

theorem Equation107_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law107.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target107]; decide)
    (by rw [ConstantTermBlockCounting.C4.target107, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation414_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law414.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target414]; decide)
    (by rw [ConstantTermBlockCounting.C4.target414, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation436_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law436.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target436]; decide)
    (by rw [PointedIdentityCounting.C4.target436, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation622_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law622.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target622]; decide)
    (by rw [PointedIdentityCounting.C4.target622, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation820_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law820.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target820]; decide)
    (by rw [PointedIdentityCounting.C4.target820, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation823_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law823.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target823]; decide)
    (by rw [PointedIdentityCounting.C4.target823, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation835_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law835.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target835]; decide)
    (by rw [PointedIdentityCounting.C4.target835, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation842_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law842.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target842]; decide)
    (by rw [PointedIdentityCounting.C4.target842, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation1036_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law1036.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target1036]; decide)
    (by rw [PointedIdentityCounting.C4.target1036, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation1225_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law1225.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target1225]; decide)
    (by rw [PointedIdentityCounting.C4.target1225, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation1226_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law1226.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target1226]; decide)
    (by rw [PointedIdentityCounting.C4.target1226, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation1248_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law1248.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target1248]; decide)
    (by rw [ConstantTermBlockCounting.C4.target1248, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation1429_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law1429.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target1429]; decide)
    (by rw [ConstantTermBlockCounting.C4.target1429, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3258_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3258.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target3258]; decide)
    (by rw [PointedIdentityCounting.C4.target3258, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3315_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3315.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target3315]; decide)
    (by rw [PointedIdentityCounting.C4.target3315, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3509_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3509.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target3509]; decide)
    (by rw [ConstantTermBlockCounting.C4.target3509, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3660_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3660.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target3660]; decide)
    (by rw [PointedIdentityCounting.C4.target3660, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3661_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3661.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target3661]; decide)
    (by rw [PointedIdentityCounting.C4.target3661, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3668_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3668.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target3668]; decide)
    (by rw [ConstantTermBlockCounting.C4.target3668, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3712_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3712.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target3712]; decide)
    (by rw [PointedIdentityCounting.C4.target3712, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation3721_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law3721.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [PointedIdentityCounting.C4.target3721]; decide)
    (by rw [PointedIdentityCounting.C4.target3721, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation4343_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law4343.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target4343]; decide)
    (by rw [ConstantTermBlockCounting.C4.target4343, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation4482_not_StructuralFrom_Equation4389_constantBlocksC4 :
    ¬ Law4482.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.C4.H) (s := ConstantTermBlockCounting.C4.left4389) (t := ConstantTermBlockCounting.C4.right4389)
    (by rw [ConstantTermBlockCounting.C4.target4482]; decide)
    (by rw [ConstantTermBlockCounting.C4.target4482, ConstantTermBlockCounting.C4.source4389]; decide)

theorem Equation1028_not_StructuralFrom_Equation4389_constantBlocksV4 :
    ¬ Law1028.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.V4.H) (s := ConstantTermBlockCounting.V4.left4389) (t := ConstantTermBlockCounting.V4.right4389)
    (by rw [ConstantTermBlockCounting.V4.target1028]; decide)
    (by rw [ConstantTermBlockCounting.V4.target1028, ConstantTermBlockCounting.V4.source4389]; decide)

theorem Equation3256_not_StructuralFrom_Equation4389_constantBlocksV4 :
    ¬ Law3256.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.V4.H) (s := ConstantTermBlockCounting.V4.left4389) (t := ConstantTermBlockCounting.V4.right4389)
    (by rw [ConstantTermBlockCounting.V4.target3256]; decide)
    (by rw [ConstantTermBlockCounting.V4.target3256, ConstantTermBlockCounting.V4.source4389]; decide)

theorem Equation3262_not_StructuralFrom_Equation4389_constantBlocksV4 :
    ¬ Law3262.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.V4.H) (s := ConstantTermBlockCounting.V4.left4389) (t := ConstantTermBlockCounting.V4.right4389)
    (by rw [ConstantTermBlockCounting.V4.target3262]; decide)
    (by rw [ConstantTermBlockCounting.V4.target3262, ConstantTermBlockCounting.V4.source4389]; decide)

theorem Equation3278_not_StructuralFrom_Equation4389_constantBlocksV4 :
    ¬ Law3278.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.V4.H) (s := ConstantTermBlockCounting.V4.left4389) (t := ConstantTermBlockCounting.V4.right4389)
    (by rw [ConstantTermBlockCounting.V4.target3278]; decide)
    (by rw [ConstantTermBlockCounting.V4.target3278, ConstantTermBlockCounting.V4.source4389]; decide)

theorem Equation3464_not_StructuralFrom_Equation4389_constantBlocksV4 :
    ¬ Law3464.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.V4.H) (s := ConstantTermBlockCounting.V4.left4389) (t := ConstantTermBlockCounting.V4.right4389)
    (by rw [ConstantTermBlockCounting.V4.target3464]; decide)
    (by rw [ConstantTermBlockCounting.V4.target3464, ConstantTermBlockCounting.V4.source4389]; decide)

theorem Equation3472_not_StructuralFrom_Equation4389_constantBlocksV4 :
    ¬ Law3472.StructuralFrom Law4389 :=
  ConstantTermBlockCounting.not_structural (H := ConstantTermBlockCounting.V4.H) (s := ConstantTermBlockCounting.V4.left4389) (t := ConstantTermBlockCounting.V4.right4389)
    (by rw [ConstantTermBlockCounting.V4.target3472]; decide)
    (by rw [ConstantTermBlockCounting.V4.target3472, ConstantTermBlockCounting.V4.source4389]; decide)

theorem Equation1248_not_StructuralFrom_Equation11_pointedIdentityC5 :
    ¬ Law1248.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term11)
    (by rw [PointedIdentityCounting.C5.target1248]; decide)
    (by rw [PointedIdentityCounting.C5.target1248, PointedIdentityCounting.C5.source11]; decide)

theorem Equation429_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law429.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target429]; decide)
    (by rw [PointedIdentityCounting.C5.target429, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1023_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1023.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1023]; decide)
    (by rw [PointedIdentityCounting.C5.target1023, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1038_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1038.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1038]; decide)
    (by rw [PointedIdentityCounting.C5.target1038, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1045_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1045.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1045]; decide)
    (by rw [PointedIdentityCounting.C5.target1045, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1048_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1048.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1048]; decide)
    (by rw [PointedIdentityCounting.C5.target1048, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1225_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1225.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1225]; decide)
    (by rw [PointedIdentityCounting.C5.target1225, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1226_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1226.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1226]; decide)
    (by rw [PointedIdentityCounting.C5.target1226, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1231_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1231.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1231]; decide)
    (by rw [PointedIdentityCounting.C5.target1231, PointedIdentityCounting.C5.source56]; decide)

theorem Equation1251_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law1251.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target1251]; decide)
    (by rw [PointedIdentityCounting.C5.target1251, PointedIdentityCounting.C5.source56]; decide)

theorem Equation3261_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law3261.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target3261]; decide)
    (by rw [PointedIdentityCounting.C5.target3261, PointedIdentityCounting.C5.source56]; decide)

theorem Equation3459_not_StructuralFrom_Equation56_pointedIdentityC5 :
    ¬ Law3459.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term56)
    (by rw [PointedIdentityCounting.C5.target3459]; decide)
    (by rw [PointedIdentityCounting.C5.target3459, PointedIdentityCounting.C5.source56]; decide)

theorem Equation436_not_StructuralFrom_Equation440_pointedIdentityC5 :
    ¬ Law436.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term440)
    (by rw [PointedIdentityCounting.C5.target436]; decide)
    (by rw [PointedIdentityCounting.C5.target436, PointedIdentityCounting.C5.source440]; decide)

theorem Equation1637_not_StructuralFrom_Equation440_pointedIdentityC5 :
    ¬ Law1637.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term440)
    (by rw [PointedIdentityCounting.C5.target1637]; decide)
    (by rw [PointedIdentityCounting.C5.target1637, PointedIdentityCounting.C5.source440]; decide)

theorem Equation1731_not_StructuralFrom_Equation440_pointedIdentityC5 :
    ¬ Law1731.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term440)
    (by rw [PointedIdentityCounting.C5.target1731]; decide)
    (by rw [PointedIdentityCounting.C5.target1731, PointedIdentityCounting.C5.source440]; decide)

theorem Equation3258_not_StructuralFrom_Equation440_pointedIdentityC5 :
    ¬ Law3258.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term440)
    (by rw [PointedIdentityCounting.C5.target3258]; decide)
    (by rw [PointedIdentityCounting.C5.target3258, PointedIdentityCounting.C5.source440]; decide)

theorem Equation3509_not_StructuralFrom_Equation440_pointedIdentityC5 :
    ¬ Law3509.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term440)
    (by rw [PointedIdentityCounting.C5.target3509]; decide)
    (by rw [PointedIdentityCounting.C5.target3509, PointedIdentityCounting.C5.source440]; decide)

theorem Equation3712_not_StructuralFrom_Equation440_pointedIdentityC5 :
    ¬ Law3712.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term440)
    (by rw [PointedIdentityCounting.C5.target3712]; decide)
    (by rw [PointedIdentityCounting.C5.target3712, PointedIdentityCounting.C5.source440]; decide)

theorem Equation1225_not_StructuralFrom_Equation643_pointedIdentityC5 :
    ¬ Law1225.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term643)
    (by rw [PointedIdentityCounting.C5.target1225]; decide)
    (by rw [PointedIdentityCounting.C5.target1225, PointedIdentityCounting.C5.source643]; decide)

theorem Equation1226_not_StructuralFrom_Equation643_pointedIdentityC5 :
    ¬ Law1226.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term643)
    (by rw [PointedIdentityCounting.C5.target1226]; decide)
    (by rw [PointedIdentityCounting.C5.target1226, PointedIdentityCounting.C5.source643]; decide)

theorem Equation414_not_StructuralFrom_Equation1049_pointedIdentityC5 :
    ¬ Law414.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term1049)
    (by rw [PointedIdentityCounting.C5.target414]; decide)
    (by rw [PointedIdentityCounting.C5.target414, PointedIdentityCounting.C5.source1049]; decide)

theorem Equation3509_not_StructuralFrom_Equation1049_pointedIdentityC5 :
    ¬ Law3509.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term1049)
    (by rw [PointedIdentityCounting.C5.target3509]; decide)
    (by rw [PointedIdentityCounting.C5.target3509, PointedIdentityCounting.C5.source1049]; decide)

theorem Equation107_not_StructuralFrom_Equation1252_pointedIdentityC5 :
    ¬ Law107.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term1252)
    (by rw [PointedIdentityCounting.C5.target107]; decide)
    (by rw [PointedIdentityCounting.C5.target107, PointedIdentityCounting.C5.source1252]; decide)

theorem Equation622_not_StructuralFrom_Equation1252_pointedIdentityC5 :
    ¬ Law622.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term1252)
    (by rw [PointedIdentityCounting.C5.target622]; decide)
    (by rw [PointedIdentityCounting.C5.target622, PointedIdentityCounting.C5.source1252]; decide)

theorem Equation1429_not_StructuralFrom_Equation1252_pointedIdentityC5 :
    ¬ Law1429.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C5.H) (t := PointedIdentityCounting.C5.term1252)
    (by rw [PointedIdentityCounting.C5.target1429]; decide)
    (by rw [PointedIdentityCounting.C5.target1429, PointedIdentityCounting.C5.source1252]; decide)
