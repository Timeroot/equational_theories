import equational_theories.Definability.StrictImplicationCounting
import equational_theories.Generated.VampireProven.Proofs10
import equational_theories.Generated.VampireProven.Proofs11

/-! Strict ordinary implications separating two remaining term-structural classes.
The small tables witness strictness; the actual term-structural obstruction is
a product of all source operations on the corresponding carrier. -/

open Law Law.MagmaLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace StrictImplicationWitnesses

/-- Table from `equational_theories/Generated/All4x4Tables/Refutation642.lean`. -/
@[implicit_reducible] def source629 : Magma (Fin 4) where
  op := ![![3, 0, 3, 1],
    ![3, 0, 3, 1],
    ![3, 2, 0, 1],
    ![3, 0, 3, 1]]

theorem source629_law : @Equation629 (Fin 4) source629 := by decide
theorem source629_not_target : ¬ @Equation52 (Fin 4) source629 := by decide

/-- Table from `equational_theories/Generated/All4x4Tables/Refutation921.lean`. -/
@[implicit_reducible] def source854 : Magma (Fin 11) where
  op := ![![2, 7, 0, 4, 6, 0, 0, 8, 7, 8, 0],
    ![2, 5, 4, 1, 2, 1, 1, 1, 5, 1, 1],
    ![2, 3, 5, 1, 2, 2, 2, 2, 5, 2, 1],
    ![3, 3, 5, 9, 3, 10, 10, 10, 5, 3, 5],
    ![6, 7, 4, 4, 6, 4, 4, 1, 7, 1, 4],
    ![5, 5, 5, 9, 5, 9, 10, 10, 5, 5, 5],
    ![6, 6, 6, 9, 6, 9, 10, 10, 6, 6, 6],
    ![6, 7, 7, 9, 6, 9, 9, 10, 7, 6, 7],
    ![2, 3, 4, 1, 2, 8, 8, 8, 5, 8, 1],
    ![10, 9, 9, 9, 6, 9, 9, 10, 9, 1, 9],
    ![10, 10, 5, 9, 10, 10, 10, 10, 5, 10, 1]]

theorem source854_law : @Equation854 (Fin 11) source854 := by decide
theorem source854_not_target : ¬ @Equation433 (Fin 11) source854 := by decide

end StrictImplicationWitnesses

theorem Equation52_not_termStructuralFromFin_Equation629_strictImplication :
    ¬ Law52.TermStructuralFromFin Law629 := by
  apply not_termStructuralFromFin_of_strict_implication
    (M := StrictImplicationWitnesses.source629)
  · intro G M h
    exact (@Law629.models_iff G M).mpr
      (@Equation52_implies_Equation629 G M ((@Law52.models_iff G M).mp h))
  · exact (@Law629.models_iff (Fin 4) StrictImplicationWitnesses.source629).mpr
      StrictImplicationWitnesses.source629_law
  · exact fun h => StrictImplicationWitnesses.source629_not_target
      ((@Law52.models_iff (Fin 4) StrictImplicationWitnesses.source629).mp h)

/-- info: 'Equation52_not_termStructuralFromFin_Equation629_strictImplication' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation52_not_termStructuralFromFin_Equation629_strictImplication

theorem Equation433_not_termStructuralFromFin_Equation854_strictImplication :
    ¬ Law433.TermStructuralFromFin Law854 := by
  apply not_termStructuralFromFin_of_strict_implication
    (M := StrictImplicationWitnesses.source854)
  · intro G M h
    exact (@Law854.models_iff G M).mpr
      (@Equation433_implies_Equation854 G M ((@Law433.models_iff G M).mp h))
  · exact (@Law854.models_iff (Fin 11) StrictImplicationWitnesses.source854).mpr
      StrictImplicationWitnesses.source854_law
  · exact fun h => StrictImplicationWitnesses.source854_not_target
      ((@Law433.models_iff (Fin 11) StrictImplicationWitnesses.source854).mp h)

/-- info: 'Equation433_not_termStructuralFromFin_Equation854_strictImplication' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation433_not_termStructuralFromFin_Equation854_strictImplication
