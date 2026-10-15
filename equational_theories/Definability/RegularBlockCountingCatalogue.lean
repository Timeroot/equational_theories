import equational_theories.Definability.RegularBlockCountsC3
import equational_theories.Definability.RegularBlockCountsC4
import equational_theories.Definability.RegularBlockCountsV4
import equational_theories.Definability.RegularBlockCountsC5

/-! Unrestricted FO-structural negatives from regular finite-group block actions.
Each count is checked by the kernel on at most 3125 small local functions. -/

open Law Law.MagmaLaw

local instance : Fact (1 < 4) := ⟨by decide⟩
local instance : Fact (1 < 5) := ⟨by decide⟩

theorem Equation99_not_StructuralFrom_Equation8_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law8 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count8]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation8_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation8_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation8_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law8 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count8]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation8_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation8_regularBlocksC3

theorem Equation1223_not_StructuralFrom_Equation8_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law8 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count8]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation8_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation8_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation8_regularBlocksC4 :
    ¬ Law1426.StructuralFrom Law8 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count1426]; decide)
    (by rw [RegularBlockCounting.C4.count1426, RegularBlockCounting.C4.count8]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation8_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation8_regularBlocksC4

theorem Equation151_not_StructuralFrom_Equation47_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law47 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count47]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation47_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation47_regularBlocksC3

theorem Equation614_not_StructuralFrom_Equation47_regularBlocksV4 :
    ¬ Law614.StructuralFrom Law47 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count614]; decide)
    (by rw [RegularBlockCounting.V4.count614, RegularBlockCounting.V4.count47]; decide)

/-- info: 'Equation614_not_StructuralFrom_Equation47_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation47_regularBlocksV4

theorem Equation817_not_StructuralFrom_Equation47_regularBlocksV4 :
    ¬ Law817.StructuralFrom Law47 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count817]; decide)
    (by rw [RegularBlockCounting.V4.count817, RegularBlockCounting.V4.count47]; decide)

/-- info: 'Equation817_not_StructuralFrom_Equation47_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation47_regularBlocksV4

theorem Equation3659_not_StructuralFrom_Equation47_regularBlocksC3 :
    ¬ Law3659.StructuralFrom Law47 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3659]; decide)
    (by rw [RegularBlockCounting.C3.count3659, RegularBlockCounting.C3.count47]; decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation47_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation47_regularBlocksC3

theorem Equation4380_not_StructuralFrom_Equation47_regularBlocksV4 :
    ¬ Law4380.StructuralFrom Law47 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count4380]; decide)
    (by rw [RegularBlockCounting.V4.count4380, RegularBlockCounting.V4.count47]; decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation47_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation47_regularBlocksV4

theorem Equation8_not_StructuralFrom_Equation99_regularBlocksV4 :
    ¬ Law8.StructuralFrom Law99 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count8]; decide)
    (by rw [RegularBlockCounting.V4.count8, RegularBlockCounting.V4.count99]; decide)

/-- info: 'Equation8_not_StructuralFrom_Equation99_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation8_not_StructuralFrom_Equation99_regularBlocksV4

theorem Equation151_not_StructuralFrom_Equation99_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law99 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count99]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation99_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation99_regularBlocksC3

theorem Equation411_not_StructuralFrom_Equation99_regularBlocksV4 :
    ¬ Law411.StructuralFrom Law99 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count411]; decide)
    (by rw [RegularBlockCounting.V4.count411, RegularBlockCounting.V4.count99]; decide)

/-- info: 'Equation411_not_StructuralFrom_Equation99_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation99_regularBlocksV4

theorem Equation1629_not_StructuralFrom_Equation151_regularBlocksV4 :
    ¬ Law1629.StructuralFrom Law151 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count1629]; decide)
    (by rw [RegularBlockCounting.V4.count1629, RegularBlockCounting.V4.count151]; decide)

/-- info: 'Equation1629_not_StructuralFrom_Equation151_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1629_not_StructuralFrom_Equation151_regularBlocksV4

theorem Equation99_not_StructuralFrom_Equation411_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law411 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count411]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation411_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation411_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation411_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law411 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count411]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation411_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation411_regularBlocksC3

theorem Equation1223_not_StructuralFrom_Equation411_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law411 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count411]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation411_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation411_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation411_regularBlocksC4 :
    ¬ Law1426.StructuralFrom Law411 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count1426]; decide)
    (by rw [RegularBlockCounting.C4.count1426, RegularBlockCounting.C4.count411]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation411_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation411_regularBlocksC4

theorem Equation3_not_StructuralFrom_Equation614_regularBlocksC3 :
    ¬ Law3.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3]; decide)
    (by rw [RegularBlockCounting.C3.count3, RegularBlockCounting.C3.count614]; decide)

/-- info: 'Equation3_not_StructuralFrom_Equation614_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation614_regularBlocksC3

theorem Equation47_not_StructuralFrom_Equation614_regularBlocksC3 :
    ¬ Law47.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count47]; decide)
    (by rw [RegularBlockCounting.C3.count47, RegularBlockCounting.C3.count614]; decide)

/-- info: 'Equation47_not_StructuralFrom_Equation614_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation614_regularBlocksC3

theorem Equation99_not_StructuralFrom_Equation614_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count614]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation614_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation614_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation614_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count614]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation614_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation614_regularBlocksC3

theorem Equation817_not_StructuralFrom_Equation614_regularBlocksV4 :
    ¬ Law817.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count817]; decide)
    (by rw [RegularBlockCounting.V4.count817, RegularBlockCounting.V4.count614]; decide)

/-- info: 'Equation817_not_StructuralFrom_Equation614_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation614_regularBlocksV4

theorem Equation1223_not_StructuralFrom_Equation614_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count614]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation614_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation614_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation614_regularBlocksC5 :
    ¬ Law1426.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C5.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C5.count1426]; decide)
    (by rw [RegularBlockCounting.C5.count1426, RegularBlockCounting.C5.count614]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation614_regularBlocksC5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation614_regularBlocksC5

theorem Equation3659_not_StructuralFrom_Equation614_regularBlocksC3 :
    ¬ Law3659.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3659]; decide)
    (by rw [RegularBlockCounting.C3.count3659, RegularBlockCounting.C3.count614]; decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation614_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation614_regularBlocksC3

theorem Equation4380_not_StructuralFrom_Equation614_regularBlocksV4 :
    ¬ Law4380.StructuralFrom Law614 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count4380]; decide)
    (by rw [RegularBlockCounting.V4.count4380, RegularBlockCounting.V4.count614]; decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation614_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation614_regularBlocksV4

theorem Equation3_not_StructuralFrom_Equation817_regularBlocksC3 :
    ¬ Law3.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3]; decide)
    (by rw [RegularBlockCounting.C3.count3, RegularBlockCounting.C3.count817]; decide)

/-- info: 'Equation3_not_StructuralFrom_Equation817_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation817_regularBlocksC3

theorem Equation47_not_StructuralFrom_Equation817_regularBlocksC3 :
    ¬ Law47.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count47]; decide)
    (by rw [RegularBlockCounting.C3.count47, RegularBlockCounting.C3.count817]; decide)

/-- info: 'Equation47_not_StructuralFrom_Equation817_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation817_regularBlocksC3

theorem Equation99_not_StructuralFrom_Equation817_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count817]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation817_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation817_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation817_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count817]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation817_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation817_regularBlocksC3

theorem Equation614_not_StructuralFrom_Equation817_regularBlocksC4 :
    ¬ Law614.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count614]; decide)
    (by rw [RegularBlockCounting.C4.count614, RegularBlockCounting.C4.count817]; decide)

/-- info: 'Equation614_not_StructuralFrom_Equation817_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation817_regularBlocksC4

theorem Equation1223_not_StructuralFrom_Equation817_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count817]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation817_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation817_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation817_regularBlocksC5 :
    ¬ Law1426.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C5.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C5.count1426]; decide)
    (by rw [RegularBlockCounting.C5.count1426, RegularBlockCounting.C5.count817]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation817_regularBlocksC5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation817_regularBlocksC5

theorem Equation3659_not_StructuralFrom_Equation817_regularBlocksC3 :
    ¬ Law3659.StructuralFrom Law817 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3659]; decide)
    (by rw [RegularBlockCounting.C3.count3659, RegularBlockCounting.C3.count817]; decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation817_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation817_regularBlocksC3

theorem Equation99_not_StructuralFrom_Equation1020_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law1020 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count1020]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation1020_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation1020_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation1020_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law1020 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count1020]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation1020_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation1020_regularBlocksC3

theorem Equation411_not_StructuralFrom_Equation1020_regularBlocksC4 :
    ¬ Law411.StructuralFrom Law1020 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count411]; decide)
    (by rw [RegularBlockCounting.C4.count411, RegularBlockCounting.C4.count1020]; decide)

/-- info: 'Equation411_not_StructuralFrom_Equation1020_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation1020_regularBlocksC4

theorem Equation1223_not_StructuralFrom_Equation1020_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law1020 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count1020]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation1020_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation1020_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation1020_regularBlocksC4 :
    ¬ Law1426.StructuralFrom Law1020 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count1426]; decide)
    (by rw [RegularBlockCounting.C4.count1426, RegularBlockCounting.C4.count1020]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation1020_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation1020_regularBlocksC4

theorem Equation3456_not_StructuralFrom_Equation1020_regularBlocksV4 :
    ¬ Law3456.StructuralFrom Law1020 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count3456]; decide)
    (by rw [RegularBlockCounting.V4.count3456, RegularBlockCounting.V4.count1020]; decide)

/-- info: 'Equation3456_not_StructuralFrom_Equation1020_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3456_not_StructuralFrom_Equation1020_regularBlocksV4

theorem Equation8_not_StructuralFrom_Equation1223_regularBlocksV4 :
    ¬ Law8.StructuralFrom Law1223 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count8]; decide)
    (by rw [RegularBlockCounting.V4.count8, RegularBlockCounting.V4.count1223]; decide)

/-- info: 'Equation8_not_StructuralFrom_Equation1223_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation8_not_StructuralFrom_Equation1223_regularBlocksV4

theorem Equation99_not_StructuralFrom_Equation1223_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law1223 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count1223]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation1223_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation1223_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation1223_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law1223 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count1223]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation1223_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation1223_regularBlocksC3

theorem Equation411_not_StructuralFrom_Equation1223_regularBlocksV4 :
    ¬ Law411.StructuralFrom Law1223 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count411]; decide)
    (by rw [RegularBlockCounting.V4.count411, RegularBlockCounting.V4.count1223]; decide)

/-- info: 'Equation411_not_StructuralFrom_Equation1223_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation1223_regularBlocksV4

theorem Equation1426_not_StructuralFrom_Equation1223_regularBlocksC4 :
    ¬ Law1426.StructuralFrom Law1223 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count1426]; decide)
    (by rw [RegularBlockCounting.C4.count1426, RegularBlockCounting.C4.count1223]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation1223_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation1223_regularBlocksC4

theorem Equation3456_not_StructuralFrom_Equation1223_regularBlocksV4 :
    ¬ Law3456.StructuralFrom Law1223 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.V4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.V4.count3456]; decide)
    (by rw [RegularBlockCounting.V4.count3456, RegularBlockCounting.V4.count1223]; decide)

/-- info: 'Equation3456_not_StructuralFrom_Equation1223_regularBlocksV4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3456_not_StructuralFrom_Equation1223_regularBlocksV4

theorem Equation8_not_StructuralFrom_Equation1426_regularBlocksC3 :
    ¬ Law8.StructuralFrom Law1426 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count8]; decide)
    (by rw [RegularBlockCounting.C3.count8, RegularBlockCounting.C3.count1426]; decide)

/-- info: 'Equation8_not_StructuralFrom_Equation1426_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation8_not_StructuralFrom_Equation1426_regularBlocksC3

theorem Equation99_not_StructuralFrom_Equation1426_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law1426 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count1426]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation1426_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation1426_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation1426_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law1426 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count1426]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation1426_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation1426_regularBlocksC3

theorem Equation411_not_StructuralFrom_Equation1426_regularBlocksC3 :
    ¬ Law411.StructuralFrom Law1426 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count411]; decide)
    (by rw [RegularBlockCounting.C3.count411, RegularBlockCounting.C3.count1426]; decide)

/-- info: 'Equation411_not_StructuralFrom_Equation1426_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation1426_regularBlocksC3

theorem Equation1020_not_StructuralFrom_Equation1426_regularBlocksC3 :
    ¬ Law1020.StructuralFrom Law1426 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1020]; decide)
    (by rw [RegularBlockCounting.C3.count1020, RegularBlockCounting.C3.count1426]; decide)

/-- info: 'Equation1020_not_StructuralFrom_Equation1426_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1020_not_StructuralFrom_Equation1426_regularBlocksC3

theorem Equation1223_not_StructuralFrom_Equation1426_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law1426 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count1426]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation1426_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation1426_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation1629_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law1629 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count1629]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation1629_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation1629_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation3253_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law3253 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count3253]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation3253_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation3253_regularBlocksC3

theorem Equation1629_not_StructuralFrom_Equation3253_regularBlocksC3 :
    ¬ Law1629.StructuralFrom Law3253 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1629]; decide)
    (by rw [RegularBlockCounting.C3.count1629, RegularBlockCounting.C3.count3253]; decide)

/-- info: 'Equation1629_not_StructuralFrom_Equation3253_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1629_not_StructuralFrom_Equation3253_regularBlocksC3

theorem Equation99_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation411_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law411.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count411]; decide)
    (by rw [RegularBlockCounting.C3.count411, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation411_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation1020_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law1020.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1020]; decide)
    (by rw [RegularBlockCounting.C3.count1020, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation1020_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1020_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation1223_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law1426.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1426]; decide)
    (by rw [RegularBlockCounting.C3.count1426, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation1629_not_StructuralFrom_Equation3456_regularBlocksC3 :
    ¬ Law1629.StructuralFrom Law3456 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1629]; decide)
    (by rw [RegularBlockCounting.C3.count1629, RegularBlockCounting.C3.count3456]; decide)

/-- info: 'Equation1629_not_StructuralFrom_Equation3456_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1629_not_StructuralFrom_Equation3456_regularBlocksC3

theorem Equation3_not_StructuralFrom_Equation4380_regularBlocksC3 :
    ¬ Law3.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3]; decide)
    (by rw [RegularBlockCounting.C3.count3, RegularBlockCounting.C3.count4380]; decide)

/-- info: 'Equation3_not_StructuralFrom_Equation4380_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation4380_regularBlocksC3

theorem Equation47_not_StructuralFrom_Equation4380_regularBlocksC3 :
    ¬ Law47.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count47]; decide)
    (by rw [RegularBlockCounting.C3.count47, RegularBlockCounting.C3.count4380]; decide)

/-- info: 'Equation47_not_StructuralFrom_Equation4380_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation4380_regularBlocksC3

theorem Equation99_not_StructuralFrom_Equation4380_regularBlocksC3 :
    ¬ Law99.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count99]; decide)
    (by rw [RegularBlockCounting.C3.count99, RegularBlockCounting.C3.count4380]; decide)

/-- info: 'Equation99_not_StructuralFrom_Equation4380_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation4380_regularBlocksC3

theorem Equation151_not_StructuralFrom_Equation4380_regularBlocksC3 :
    ¬ Law151.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count151]; decide)
    (by rw [RegularBlockCounting.C3.count151, RegularBlockCounting.C3.count4380]; decide)

/-- info: 'Equation151_not_StructuralFrom_Equation4380_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation4380_regularBlocksC3

theorem Equation614_not_StructuralFrom_Equation4380_regularBlocksC4 :
    ¬ Law614.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C4.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C4.count614]; decide)
    (by rw [RegularBlockCounting.C4.count614, RegularBlockCounting.C4.count4380]; decide)

/-- info: 'Equation614_not_StructuralFrom_Equation4380_regularBlocksC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation4380_regularBlocksC4

theorem Equation1223_not_StructuralFrom_Equation4380_regularBlocksC3 :
    ¬ Law1223.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count1223]; decide)
    (by rw [RegularBlockCounting.C3.count1223, RegularBlockCounting.C3.count4380]; decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation4380_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation4380_regularBlocksC3

theorem Equation1426_not_StructuralFrom_Equation4380_regularBlocksC5 :
    ¬ Law1426.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C5.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C5.count1426]; decide)
    (by rw [RegularBlockCounting.C5.count1426, RegularBlockCounting.C5.count4380]; decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation4380_regularBlocksC5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation4380_regularBlocksC5

theorem Equation3659_not_StructuralFrom_Equation4380_regularBlocksC3 :
    ¬ Law3659.StructuralFrom Law4380 :=
  RegularBlockCounting.not_structural (H := RegularBlockCounting.C3.H) (by decide) (by decide)
    (by rw [RegularBlockCounting.C3.count3659]; decide)
    (by rw [RegularBlockCounting.C3.count3659, RegularBlockCounting.C3.count4380]; decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation4380_regularBlocksC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation4380_regularBlocksC3

