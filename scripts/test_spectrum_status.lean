import equational_theories.Spectrum.Status
import Lean.Elab.Tactic.Decide

/-! Negative regression tests for the proof-status audit; not imported by the library. -/
namespace SpectrumStatusTest

theorem good : True := True.intro
spectrum_assert good complete

axiom undocumented : True
theorem usesUndocumented : True := undocumented
/-- error: SpectrumStatusTest.usesUndocumented: undocumented axioms/dependencies [SpectrumStatusTest.undocumented] -/
#guard_msgs in
spectrum_assert usesUndocumented complete

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem gap : True := by sorry
/-- error: SpectrumStatusTest.gap: undocumented axioms/dependencies [sorryAx] -/
#guard_msgs in
spectrum_assert gap complete

spectrum_pending gap noteGap "Regression test" "Intentionally omitted argument."
spectrum_assert gap noteGap
theorem inheritsGap : True := gap
spectrum_assert inheritsGap noteGap
/-- error: SpectrumStatusTest.inheritsGap: expected Spectrum.Status.Evidence.complete, found Spectrum.Status.Evidence.noteGap; pending=[SpectrumStatusTest.gap] -/
#guard_msgs in
spectrum_assert inheritsGap complete

theorem untagged : 2 + 2 = 4 := by native_decide
/-- error: SpectrumStatusTest.untagged: undocumented axioms/dependencies [SpectrumStatusTest.untagged._native.native_decide.ax_1_1] -/
#guard_msgs in
spectrum_assert untagged complete

@[spectrum_native]
theorem tagged : 2 + 2 = 4 := by native_decide
spectrum_assert tagged complete

/-- error: SpectrumStatusTest.good has no proof gap; remove its pending annotation -/
#guard_msgs in
spectrum_pending good proofAvailable "Regression test" "Already proved."

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem available : True := by sorry
spectrum_pending available proofAvailable "Regression test" "Formalization omitted."
spectrum_assert available proofAvailable
theorem mixed : True ∧ True := ⟨available, gap⟩
spectrum_assert mixed noteGap

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem hidesExtraAxiom : True ∧ True := ⟨undocumented, by sorry⟩
/-- error: Unapproved axiom SpectrumStatusTest.undocumented in pending declaration SpectrumStatusTest.hidesExtraAxiom -/
#guard_msgs in
spectrum_pending hidesExtraAxiom proofAvailable "Regression test" "Must not hide an extra axiom."

end SpectrumStatusTest
