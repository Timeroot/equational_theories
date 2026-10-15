import equational_theories.Parastrophes

/-! Attribute acceptance and rejection tests. These are deliberately outside the
library imports: failed annotations must not enter the exported catalogue. -/
open Parastrophes Law

/-- error: Expected QuasigroupLaw, SingleEquation, Characterizes, TermRecovery, UniformTermRecovery, or UniformTermWitness (or a negation of a question) -/
#guard_msgs in
@[parastrophe_result] theorem wrongQuestionShape : True := trivial

/-- error: Refuting one target equation or one term does not refute existence; negate SingleEquation or UniformTermRecovery instead -/
#guard_msgs in
@[parastrophe_result] theorem excludedTargetIsNotGlobalNegative :
    ¬ Characterizes .all Law543 .right Law1 := by
  intro h
  exact Catalogue.right_noSingleEquation543 ⟨Law1, h⟩

/-- error: Parastrophe attributes require a theorem -/
#guard_msgs in
@[parastrophe_result] def definitionIsNotEvidence : QuasigroupLaw .all Law2 := Catalogue.quasigroup2

/-- error: A parastrophe claim needs a docstring explaining the purported proof -/
#guard_msgs in
@[parastrophe_claim] theorem unexplainedClaim : QuasigroupLaw .all Law2 := Catalogue.quasigroup2

-- A correctly typed theorem is accepted, with metadata obtained from its type.
@[parastrophe_result] theorem acceptedFiniteRestriction : QuasigroupLaw .fin Law543 :=
  quasigroup_finite Catalogue.quasigroup543

run_elab do
  let entries := results.getState (← Lean.getEnv)
  unless entries.any (fun e => e.name == "acceptedFiniteRestriction" && e.equation == 543 &&
      e.scope == "fin" && e.kind == "quasigroup" && e.positive && e.status == "PROVED") do
    throwError "Accepted parastrophe theorem was not exported with its exact question"
  for n in ["wrongQuestionShape", "excludedTargetIsNotGlobalNegative", "definitionIsNotEvidence", "unexplainedClaim"] do
    if entries.any (fun e => e.name == n) then throwError "Rejected declaration entered the catalogue: {n}"
