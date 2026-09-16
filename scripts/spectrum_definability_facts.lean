import equational_theories.Spectrum

/-!
Read-only input to `spectrum_definability_check.py`. Inspect actual declaration
types and transitive proof dependencies, never names alone. Emit completed
concrete model/exclusion facts and spectrum inclusions/equalities as JSON lines.
Also instantiate unconditional one-Nat-parameter construction families at 0..5;
these cover all their values at the relevant small orders 2..5.
Pending declarations (including aliases depending on them) are not evidence.
The separate `check_spectrum.lean` validates every catalogue formula and status.
-/

set_option maxHeartbeats 0

open Lean Meta Elab Command

private def lawId? (e : Expr) : Option Nat := do
  let .const name _ := e | none
  let text := name.toString
  if text.startsWith "Law" then text.drop 3 |>.toString.toNat? else none

private def spectrumLaw? (e : Expr) : Option Nat := do
  if e.isAppOf ``Law.MagmaLaw.spectrum then lawId? e.getAppArgs[1]! else none

private partial def fact? (type : Expr) : MetaM (Option Json) := do
  let args := type.getAppArgs
  if type.isAppOf ``Law.MagmaLaw.HasModel then
    if let some law := lawId? args[1]! then
      if let .lit (.natVal n) := ← whnf args[2]! then
        return some <| toJson ("model", law, n)
  if type.isAppOf ``Not then
    if let some fact ← fact? args[0]! then
      if let .ok (kind, law, n) := fromJson? (α := String × Nat × Nat) fact then
        if kind == "model" then return some <| toJson ("excluded", law, n)
  if type.isAppOf ``Law.MagmaLaw.HasFullSpectrum then
    if let some law := lawId? args[1]! then
      return some <| toJson ("full", law, 0)
  if type.isAppOf ``Law.MagmaLaw.Subspectral then
    if let some source := lawId? args[2]! then
      if let some target := lawId? args[3]! then
        return some <| toJson ("inclusion", source, target)
  if type.isAppOf ``Eq then
    if let some source := spectrumLaw? args[1]! then
      if let some target := spectrumLaw? args[2]! then
        return some <| toJson ("equal", source, target)
  return none

run_elab do
  let mut checked : NameMap Spectrum.Status.Summary := {}
  let mut pending : Nat := 0
  for (name, ci) in (← getEnv).constants.toList do
    unless name.toString.startsWith "Spectrum." do continue
    unless ci matches .thmInfo _ do continue
    let (summary, cache) := ((Spectrum.Status.analyse name).run (← getEnv)).run checked
    checked := cache
    unless summary.bad.isEmpty do throwError "Unapproved axioms: {name}: {summary.bad}"
    unless summary.pending.isEmpty do
      pending := pending + 1
      continue
    if let some fact ← fact? ci.type then
      IO.println <| (Json.mkObj [("theorem", toJson name.toString), ("fact", fact)]).compress
    if let .forallE _ domain body _ := ci.type then
      if domain.isConstOf ``Nat then
        for k in [:6] do
          if let some fact ← fact? (body.instantiate1 (mkNatLit k)) then
            IO.println <| (Json.mkObj [("theorem", toJson s!"{name} {k}"),
              ("fact", fact)]).compress
  IO.println <| (Json.mkObj [("pending_declarations_skipped", toJson pending)]).compress
