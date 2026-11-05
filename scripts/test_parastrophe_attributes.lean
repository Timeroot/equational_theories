import equational_theories.Parastrophes

/-! Attribute acceptance and rejection tests. These are deliberately outside the
library imports: failed annotations must not enter the exported catalogue. -/
open Parastrophes Law

/-- error: Expected an unconditional CharacterizesBasis theorem -/
#guard_msgs in
@[parastrophe_basis] theorem conditionalBasis
    (h : CharacterizesBasis .fin Law872 .left [Law614, ImageBasisCatalogue.cross872]) :
    CharacterizesBasis .fin Law872 .left [Law614, ImageBasisCatalogue.cross872] := h

/-- error: An image basis must be a theorem -/
#guard_msgs in
@[parastrophe_basis] def basisDefinition :
    CharacterizesBasis .fin Law872 .left [Law614, ImageBasisCatalogue.cross872] :=
  ImageBasisCatalogue.left872_fin

@[parastrophe_basis] theorem acceptedImageBasis :
    CharacterizesBasis .fin Law872 .left [Law614, ImageBasisCatalogue.cross872] :=
  ImageBasisCatalogue.left872_fin

run_elab do
  let entries := imageBases.getState (← Lean.getEnv)
  unless entries.any (fun e => e.name == "acceptedImageBasis" && e.equation == 872 &&
      e.scope == "fin" && e.side == "left" && e.targetLaws.length == 2) do
    throwError "Missing exact multi-equation basis"
  for name in ["conditionalBasis", "basisDefinition"] do
    if entries.any (fun e => e.name == name) then throwError "Rejected basis entered export"
  if (results.getState (← Lean.getEnv)).any (fun e => e.name == "acceptedImageBasis") then
    throwError "A multiple-equation basis was incorrectly recorded as a single equation"

/-- error: Expected QuasigroupLaw, SideQuasigroupLaw, SingleEquation, Characterizes, TermRecovery, UniformTermRecovery, or UniformTermWitness (or a negation of a question) -/
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

-- Side metadata is part of the theorem type, never inferred from its name.
@[parastrophe_result] theorem acceptedLeftOnly : SideQuasigroupLaw .fin Law677 .left :=
  termRecovery_sideQuasigroup (uniform_implies_term ⟨_, Catalogue.left_term677_fin⟩)

@[parastrophe_result] theorem acceptedSideNegative : ¬ SideQuasigroupLaw .fin Law4 .left :=
  Catalogue.not_leftQuasigroup4

run_elab do
  let entries := results.getState (← Lean.getEnv)
  unless entries.any (fun e => e.name == "acceptedLeftOnly" && e.kind == "sideQuasigroup" &&
      e.side == some "left" && e.scope == "fin" && e.positive) do
    throwError "Missing one-sided positive metadata"
  unless entries.any (fun e => e.name == "acceptedSideNegative" && e.kind == "sideQuasigroup" &&
      e.side == some "left" && !e.positive) do
    throwError "Missing one-sided negative metadata"
