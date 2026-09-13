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
  unless full == 3074 && noTwo == 1558 && noThree == 62 do
    throwError "Unexpected classification counts: {full}, {noTwo}, {noThree}"
  logInfo m!"Verified all 4694 laws: {full} full spectra, {noTwo} exclude 2, {noThree} exclude 3."

-- Representative constructive, exhaustive, structural-transfer and exact proofs.
#print axioms Spectrum.full_492
#print axioms Spectrum.full_1682
#print axioms Spectrum.not_two_677
#print axioms Spectrum.not_three_1485
#print axioms Spectrum.spectrum_1685
#print axioms Spectrum.spectrum_546_eq_556

open Lean Meta Elab Command Spectrum in
run_elab do
  let data ← IO.FS.readFile "data/spectrum.json"
  let records ← ofExcept ((Json.parse data).bind Json.getArr?)
  unless records.size == 4694 do throwError "The catalogue must have 4694 records"
  let mut exactCount : Nat := 0
  let mut provedCount : Nat := 0
  let mut unknownCount : Nat := 0
  let mut boundsProved : Nat := 0
  let mut boundsDeferred : Nat := 0
  -- Reuse the visited set only for dependencies already certified sorry-free.
  -- Deferred proofs are never inserted into this cache.
  let checkedProofs ← IO.mkRef ({} : Lean.CollectAxioms.State)
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
      let cached ← checkedProofs.get
      let (_, state) := ((Lean.CollectAxioms.collect name).run (← getEnv)).run
        { cached with axioms := #[] }
      let axioms := state.axioms
      let hasSorry := axioms.contains ``sorryAx
      unless hasSorry == (status == "DEFERRED") do
        throwError "Proof status mismatch for {name}: status={status}, axioms={axioms}"
      for ax in axioms do
        unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx] do
          throwError "Unapproved axiom {ax} in {name}"
      if status == "PROVED" then checkedProofs.set state
    if status == "EXACT" then
      exactCount := exactCount + 1
      let name := (← getString "exact_spectrum_theorem").toName
      checkType name (← mkEq spec (← formulaExpr "exact_spectrum_formula"))
      let proofStatus ← getString "exact_proof_status"
      checkAxioms name proofStatus
      if proofStatus == "PROVED" then provedCount := provedCount + 1
    else
      unless status == "UNKNOWN" do throwError "Invalid mathematical status for E{i}"
      unknownCount := unknownCount + 1
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
  unless exactCount == 4628 && provedCount == 4574 && unknownCount == 66 do
    throwError "Unexpected exact coverage: {exactCount}, {provedCount}, {unknownCount}"
  logInfo m!"Catalogue: {exactCount} exact formulas ({provedCount} proved, {exactCount - provedCount} deferred); {unknownCount} genuinely UNKNOWN."
  logInfo m!"UNKNOWN bounds: {boundsProved} proved, {boundsDeferred} deferred. All declaration types and transitive axioms checked."

#print axioms Spectrum.Catalogue.exact_474
#print axioms Spectrum.Catalogue.exact_168
#print axioms Spectrum.not_order_1480_3
