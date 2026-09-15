import equational_theories.Spectrum
import Lean.Util.CollectAxioms

set_option maxHeartbeats 8000000

/-!
Check coverage against the actual Lean declaration types, not just theorem names
or the generator's arithmetic. Run with `lake env lean scripts/check_spectrum.lean`.
-/

open Lean Meta Elab Command in
run_elab do
  let mut full : Nat := 0
  let mut noTwo : Nat := 0
  let mut noThree : Nat := 0
  let mut checked : NameMap Spectrum.Status.Summary := {}
  for i in [1:4695] do
    let law := mkConst (.mkSimple s!"Law{i}")
    let fullName := `Spectrum |>.str s!"full_{i}"
    let twoName := `Spectrum |>.str s!"not_two_{i}"
    let threeName := `Spectrum |>.str s!"not_three_{i}"
    let candidates := [fullName, twoName, threeName].filter (← getEnv).contains
    unless candidates.length == 1 do
      throwError "Equation {i}: expected exactly one full-spectrum or exclusion certificate"
    let name := candidates.head!
    let expected ← if name == fullName then
      full := full + 1
      mkAppM ``Law.MagmaLaw.HasFullSpectrum #[law]
    else
      let n := if name == twoName then 2 else 3
      if n == 2 then noTwo := noTwo + 1 else noThree := noThree + 1
      pure <| mkApp (mkConst ``Not) (← mkAppM ``Law.MagmaLaw.HasModel #[law, mkNatLit n])
    unless ← isDefEq (← getConstInfo name).type expected do
      throwError "Equation {i}: incorrect certificate type for {name}"
    let (summary, cache) := ((Spectrum.Status.analyse name).run (← getEnv)).run checked
    checked := cache
    unless summary.bad.isEmpty && summary.pending.isEmpty do
      throwError "Incomplete classification certificate {name}: {summary.bad}, {summary.pending}"
  unless full == 3074 && noTwo == 1558 && noThree == 62 do
    throwError "Unexpected classification counts: {full}, {noTwo}, {noThree}"
  logInfo m!"Verified all 4694 laws: {full} full spectra, {noTwo} exclude 2, {noThree} exclude 3."

open Lean Meta Elab Command Spectrum in
run_elab do
  let data ← IO.FS.readFile "data/spectrum/catalogue.json"
  let records ← ofExcept ((Json.parse data).bind Json.getArr?)
  unless records.size == 4694 do throwError "The catalogue must have 4694 records"
  let mut exactCount : Nat := 0
  let mut provedCount : Nat := 0
  let mut availableCount : Nat := 0
  let mut gapCount : Nat := 0
  let mut unknownCount : Nat := 0
  let mut boundsProved : Nat := 0
  let mut boundsDeferred : Nat := 0
  let checkedProofs ← IO.mkRef ({} : NameMap Status.Summary)
  let openIds := Catalogue.openProblems.map (·.equation)
  unless Catalogue.openProblems.all (·.evidence == .mathematicallyOpen) do
    throwError "Incorrect category in the Lean open-problem registry"
  for idx in [:records.size] do
    let record := records[idx]!
    let i ← ofExcept ((record.getObjVal? "equation").bind Json.getNat?)
    unless i == idx + 1 do throwError "Catalogue order mismatch at {idx}"
    let getString := fun key => Lean.ofExcept ((record.getObjVal? key).bind Json.getStr?)
    let status ← getString "mathematical_status"
    let law := mkConst (.mkSimple s!"Law{i}")
    let spec ← mkAppM ``Law.MagmaLaw.spectrum #[law]
    let checkType := fun (name : Name) (expected : Expr) => do
      unless ← isDefEq (← getConstInfo name).type expected do
        throwError "Wrong catalogue type for {name}"
    let formulaExpr := fun (key : String) => do
      let formula ← getString key
      let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term formula)
      Term.elabTerm stx (some (mkApp (mkConst ``Set [levelZero]) (mkConst ``Nat)))
    let checkAxioms := fun (name : Name) (status : String) => do
      let (summary, cache) := ((Status.analyse name).run (← getEnv)).run (← checkedProofs.get)
      checkedProofs.set cache
      unless summary.bad.isEmpty do throwError "Unapproved axioms in {name}: {summary.bad}"
      let expected ← match status with
        | "PROVED" => pure Status.Evidence.complete
        | "PROOF_AVAILABLE" => pure Status.Evidence.proofAvailable
        | "NOTE_GAP" => pure Status.Evidence.noteGap
        | _ => throwError "Invalid proof status {status} for {name}"
      unless summary.evidence (← getEnv) == expected do
        throwError "Proof status mismatch for {name}: JSON={status}, pending={summary.pending}"
    if status == "EXACT" then
      exactCount := exactCount + 1
      let name := (← getString "exact_spectrum_theorem").toName
      checkType name (← mkEq spec (← formulaExpr "exact_spectrum_formula"))
      let proofStatus ← getString "exact_proof_status"
      checkAxioms name proofStatus
      if proofStatus == "PROVED" then provedCount := provedCount + 1
      if proofStatus == "PROOF_AVAILABLE" then availableCount := availableCount + 1
      if proofStatus == "NOTE_GAP" then gapCount := gapCount + 1
      if openIds.contains i then throwError "Exact formula E{i} is in the open-problem registry"
    else
      unless status == "UNKNOWN" do throwError "Invalid mathematical status for E{i}"
      unknownCount := unknownCount + 1
      unless openIds.contains i do throwError "Missing E{i} from Lean's open-problem registry"
      if (← getEnv).contains (`Spectrum.Catalogue |>.str s!"exact_{i}") then
        throwError "An UNKNOWN spectrum must not have an exact theorem: E{i}"
      for kind in ["lower", "upper"] do
        let name := (← getString s!"{kind}_bound_theorem").toName
        let formula ← formulaExpr s!"{kind}_bound_formula"
        let expected ← if kind == "lower" then mkAppM ``Set.Subset #[formula, spec]
                       else mkAppM ``Set.Subset #[spec, formula]
        checkType name expected
        let proofStatus ← getString s!"{kind}_bound_proof_status"
        checkAxioms name proofStatus
        if proofStatus == "PROVED" then boundsProved := boundsProved + 1
        else boundsDeferred := boundsDeferred + 1
      if (← getString "cofinite_status") == "KNOWN" then
        let name := (← getString "cofinite_theorem").toName
        checkType name (← mkAppM ``Spectrum.CofiniteSpectrum #[law])
        checkAxioms name (← getString "cofinite_proof_status")
      else if (← getEnv).contains (`Spectrum.Catalogue |>.str s!"cofinite_{i}") then
        throwError "Unknown/disputed cofiniteness must not have a theorem: E{i}"
  unless exactCount == 4628 && provedCount == 4574 && unknownCount == 66 do
    throwError "Unexpected exact coverage: {exactCount}, {provedCount}, {unknownCount}"
  unless availableCount == 24 && gapCount == 30 && openIds.length == unknownCount do
    throwError "Unexpected evidence counts: available={availableCount}, gaps={gapCount}, open={openIds.length}"
  logInfo m!"Catalogue: {exactCount} exact formulas ({provedCount} proved, {availableCount} proofs available, {gapCount} unreconstructed note gaps); {unknownCount} exact spectra open in the note."
  logInfo m!"UNKNOWN bounds: {boundsProved} proved, {boundsDeferred} deferred. All declaration types and transitive axioms checked."
