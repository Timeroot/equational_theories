import equational_theories.Parastrophes
import Lean.DeclarationRange

/-! Small standalone export; the default website builder includes this step. -/
open Lean Elab Command

private def sourceRef (name : Name) : Lean.Elab.Term.TermElabM Json := do
  let env ← getEnv
  let some moduleIdx := env.getModuleIdxFor? name | throwError "No module for {name}"
  let file := env.header.moduleNames[moduleIdx.toNat]!.toString.replace "." "/" ++ ".lean"
  let some range ← findDeclarationRanges? name | throwError "No source range for {name}"
  return Json.mkObj [("name", toJson name.toString), ("file", toJson file),
    ("line", toJson range.selectionRange.pos.line), ("status", toJson "PROVED")]

run_elab do
  let env ← getEnv
  let entries ← (Parastrophes.results.getState env).mapM fun entry => do
    let name := entry.name.toName
    let some moduleIdx := env.getModuleIdxFor? name | throwError "No module for {name}"
    let file := env.header.moduleNames[moduleIdx.toNat]!.toString.replace "." "/" ++ ".lean"
    let some range ← findDeclarationRanges? name | throwError "No source range for {name}"
    -- An attribute may be applied from a different module. Link the theorem's
    -- declaration, not just the place where somebody registered its metadata.
    pure { entry with file := file, line := range.selectionRange.pos.line }
  let ruleNames : Array Name := #[
    ``Parastrophes.imageBasis_finite, ``Parastrophes.imageBasis_dual,
    ``Parastrophes.imageBasis_of_equivalent,
    ``Parastrophes.quasigroup_finite, ``Parastrophes.singleEquation_finite,
    ``Parastrophes.termRecovery_finite, ``Parastrophes.uniformTermRecovery_finite,
    ``Parastrophes.quasigroup_dual, ``Parastrophes.singleEquation_dual,
    ``Parastrophes.termRecovery_dual, ``Parastrophes.uniformTermRecovery_dual,
    ``Parastrophes.uniform_implies_term, ``Parastrophes.termRecovery_quasigroup, ``Parastrophes.termRecovery_iff_uniform_all,
    ``Parastrophes.quasigroup_uniform_all, ``Parastrophes.quasigroup_term_fin, ``Parastrophes.characterizes_quasigroup,
    ``Parastrophes.quasigroup_of_implies, ``Parastrophes.termRecovery_of_implies,
    ``Parastrophes.uniformTermRecovery_of_implies, ``Parastrophes.singleEquation_of_equivalent,
    ``Parastrophes.characterizes_self, ``Parastrophes.characterizes_opposite,
    ``Parastrophes.sideQuasigroup_finite, ``Parastrophes.sideQuasigroup_dual,
    ``Parastrophes.sideQuasigroup_of_implies, ``Parastrophes.quasigroup_side,
    ``Parastrophes.sideQuasigroups_quasigroup, ``Parastrophes.termRecovery_sideQuasigroup,
    ``Parastrophes.sideQuasigroup_uniform_all, ``Parastrophes.sideQuasigroup_term_fin,
    ``Parastrophes.characterizes_sideQuasigroup, ``Parastrophes.characterizes_symm,
    ``Parastrophes.division_symm, ``Parastrophes.division_opposite,
    ``Parastrophes.division_otherSide_iff, ``Parastrophes.right_after_left,
    ``Parastrophes.left_after_right, ``Parastrophes.characterizes_otherSide]
  let mut rules : Array Json := #[]
  for name in ruleNames do
    for ax in ← Lean.collectAxioms name do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unproved parastrophe transfer rule {name}: {ax}"
    let some moduleIdx := env.getModuleIdxFor? name | throwError "No module for {name}"
    let file := env.header.moduleNames[moduleIdx.toNat]!.toString.replace "." "/" ++ ".lean"
    let some range ← findDeclarationRanges? name | throwError "No source range for {name}"
    rules := rules.push <| Json.mkObj [("name", toJson name.toString), ("file", toJson file),
      ("line", toJson range.selectionRange.pos.line), ("status", toJson "PROVED")]
  let output := (← IO.getEnv "WEBSITE_PARASTROPHES").getD "/tmp/website-parastrophes.json"
  let bases ← (Parastrophes.imageBases.getState env).mapM fun entry => do
    let name := entry.name.toName
    let some moduleIdx := env.getModuleIdxFor? name | throwError "No module for {name}"
    let file := env.header.moduleNames[moduleIdx.toNat]!.toString.replace "." "/" ++ ".lean"
    let some range ← findDeclarationRanges? name | throwError "No source range for {name}"
    pure { entry with file := file, line := range.selectionRange.pos.line }
  let consequences := Parastrophes.consequences.getState env
  let mut consequenceSources : Array Json := #[]
  let mut seen : NameSet := {}
  for entry in consequences do
    for ax in ← Lean.collectAxioms entry.name.toName do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unproved generated consequence {entry.name}: {ax}"
    for ref in entry.refs do
      unless seen.contains ref.toName do
        seen := seen.insert ref.toName
        consequenceSources := consequenceSources.push (← sourceRef ref.toName)
  IO.FS.writeFile output (Json.mkObj [("version", toJson (2 : Nat)),
    ("records", toJson entries), ("rules", toJson rules),
    ("imageBases", toJson bases),
    ("consequences", toJson consequences), ("consequenceSources", toJson consequenceSources)]).compress
  IO.println s!"Exported {entries.size} checked parastrophe records, {rules.size} transfer rules, and {consequences.size} generated consequences to {output}"
