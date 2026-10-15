import equational_theories.Definability.PairSwapCounting

/-! New unrestricted FO-structural negatives from independently swappable pairs.

A unary law with c admissible local tables has exactly c^m · 4^(m(m-1)) tables
invariant under the independent swaps of m pairs. A strict decrease in c
contradicts the uniform counting bound supplied by FO compactness.

The kernel checks only the four Boolean local tables; the argument for arbitrary
numbers of pairs is symbolic. These results make no claim about finite-only FO
structure, nor about definitions without recovery of the source operation.
-/

open Law Law.MagmaLaw

theorem Equation47_not_StructuralFrom_Equation8_pairSwaps :
    ¬ Law47.StructuralFrom Law8 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation47_not_StructuralFrom_Equation8_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation8_pairSwaps

theorem Equation614_not_StructuralFrom_Equation8_pairSwaps :
    ¬ Law614.StructuralFrom Law8 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation8_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation8_pairSwaps

theorem Equation817_not_StructuralFrom_Equation8_pairSwaps :
    ¬ Law817.StructuralFrom Law8 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation8_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation8_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation8_pairSwaps :
    ¬ Law3659.StructuralFrom Law8 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation8_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation8_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation8_pairSwaps :
    ¬ Law4380.StructuralFrom Law8 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation8_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation8_pairSwaps

theorem Equation3_not_StructuralFrom_Equation99_pairSwaps :
    ¬ Law3.StructuralFrom Law99 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3_not_StructuralFrom_Equation99_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation99_pairSwaps

theorem Equation47_not_StructuralFrom_Equation99_pairSwaps :
    ¬ Law47.StructuralFrom Law99 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation47_not_StructuralFrom_Equation99_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation99_pairSwaps

theorem Equation614_not_StructuralFrom_Equation99_pairSwaps :
    ¬ Law614.StructuralFrom Law99 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation99_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation99_pairSwaps

theorem Equation817_not_StructuralFrom_Equation99_pairSwaps :
    ¬ Law817.StructuralFrom Law99 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation99_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation99_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation99_pairSwaps :
    ¬ Law3659.StructuralFrom Law99 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation99_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation99_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation99_pairSwaps :
    ¬ Law4380.StructuralFrom Law99 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation99_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation99_pairSwaps

theorem Equation99_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law99.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation99_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation151_pairSwaps

theorem Equation614_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law614.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation151_pairSwaps

theorem Equation817_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law817.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation151_pairSwaps

theorem Equation1020_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law1020.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1020_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1020_not_StructuralFrom_Equation151_pairSwaps

theorem Equation1223_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law1223.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation151_pairSwaps

theorem Equation1426_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law1426.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation151_pairSwaps

theorem Equation3456_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law3456.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3456_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3456_not_StructuralFrom_Equation151_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law3659.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation151_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation151_pairSwaps :
    ¬ Law4380.StructuralFrom Law151 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation151_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation151_pairSwaps

theorem Equation614_not_StructuralFrom_Equation411_pairSwaps :
    ¬ Law614.StructuralFrom Law411 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation411_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation411_pairSwaps

theorem Equation817_not_StructuralFrom_Equation411_pairSwaps :
    ¬ Law817.StructuralFrom Law411 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation411_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation411_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation411_pairSwaps :
    ¬ Law3659.StructuralFrom Law411 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation411_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation411_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation411_pairSwaps :
    ¬ Law4380.StructuralFrom Law411 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation411_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation411_pairSwaps

theorem Equation614_not_StructuralFrom_Equation1020_pairSwaps :
    ¬ Law614.StructuralFrom Law1020 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation1020_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation1020_pairSwaps

theorem Equation817_not_StructuralFrom_Equation1020_pairSwaps :
    ¬ Law817.StructuralFrom Law1020 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation1020_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation1020_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation1020_pairSwaps :
    ¬ Law3659.StructuralFrom Law1020 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation1020_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation1020_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation1020_pairSwaps :
    ¬ Law4380.StructuralFrom Law1020 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation1020_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation1020_pairSwaps

theorem Equation3_not_StructuralFrom_Equation1223_pairSwaps :
    ¬ Law3.StructuralFrom Law1223 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3_not_StructuralFrom_Equation1223_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation1223_pairSwaps

theorem Equation47_not_StructuralFrom_Equation1223_pairSwaps :
    ¬ Law47.StructuralFrom Law1223 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation47_not_StructuralFrom_Equation1223_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation1223_pairSwaps

theorem Equation614_not_StructuralFrom_Equation1223_pairSwaps :
    ¬ Law614.StructuralFrom Law1223 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation1223_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation1223_pairSwaps

theorem Equation817_not_StructuralFrom_Equation1223_pairSwaps :
    ¬ Law817.StructuralFrom Law1223 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation1223_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation1223_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation1223_pairSwaps :
    ¬ Law3659.StructuralFrom Law1223 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation1223_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation1223_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation1223_pairSwaps :
    ¬ Law4380.StructuralFrom Law1223 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation1223_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation1223_pairSwaps

theorem Equation3_not_StructuralFrom_Equation1426_pairSwaps :
    ¬ Law3.StructuralFrom Law1426 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3_not_StructuralFrom_Equation1426_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation1426_pairSwaps

theorem Equation47_not_StructuralFrom_Equation1426_pairSwaps :
    ¬ Law47.StructuralFrom Law1426 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation47_not_StructuralFrom_Equation1426_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation1426_pairSwaps

theorem Equation614_not_StructuralFrom_Equation1426_pairSwaps :
    ¬ Law614.StructuralFrom Law1426 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation1426_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation1426_pairSwaps

theorem Equation817_not_StructuralFrom_Equation1426_pairSwaps :
    ¬ Law817.StructuralFrom Law1426 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation1426_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation1426_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation1426_pairSwaps :
    ¬ Law3659.StructuralFrom Law1426 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation1426_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation1426_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation1426_pairSwaps :
    ¬ Law4380.StructuralFrom Law1426 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation1426_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation1426_pairSwaps

theorem Equation99_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law99.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation99_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation411_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law411.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation411_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation614_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law614.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation817_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law817.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation1020_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law1020.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1020_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1020_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation1223_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law1223.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation1426_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law1426.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation3456_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law3456.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3456_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3456_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law3659.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation1629_pairSwaps :
    ¬ Law4380.StructuralFrom Law1629 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation1629_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation1629_pairSwaps

theorem Equation99_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law99.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation99_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation99_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation614_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law614.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation817_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law817.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation1020_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law1020.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1020_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1020_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation1223_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law1223.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1223_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1223_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation1426_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law1426.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation1426_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1426_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation3456_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law3456.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3456_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3456_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law3659.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation3253_pairSwaps :
    ¬ Law4380.StructuralFrom Law3253 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation3253_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation3253_pairSwaps

theorem Equation614_not_StructuralFrom_Equation3456_pairSwaps :
    ¬ Law614.StructuralFrom Law3456 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation614_not_StructuralFrom_Equation3456_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_StructuralFrom_Equation3456_pairSwaps

theorem Equation817_not_StructuralFrom_Equation3456_pairSwaps :
    ¬ Law817.StructuralFrom Law3456 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation817_not_StructuralFrom_Equation3456_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_StructuralFrom_Equation3456_pairSwaps

theorem Equation3659_not_StructuralFrom_Equation3456_pairSwaps :
    ¬ Law3659.StructuralFrom Law3456 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation3659_not_StructuralFrom_Equation3456_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation3456_pairSwaps

theorem Equation4380_not_StructuralFrom_Equation3456_pairSwaps :
    ¬ Law4380.StructuralFrom Law3456 :=
  PairSwapCounting.not_structural (by decide) (by decide) (by decide) (by decide)

/-- info: 'Equation4380_not_StructuralFrom_Equation3456_pairSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4380_not_StructuralFrom_Equation3456_pairSwaps

