import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms

import equational_theories.ParseImplications

/-!
This file defines the @[equational_result] attribute, intended for marking theorems that
represent edges in the implication graph.

At one point we discussed getting the same information by scanning through the environment
and collecting all theorems that have the correct shape.
See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Refactoring.20the.20Lean.20file.20structure/near/473148427.

That approach would have the advantage of allowing the theorems to be more succinct in the
source code (no need to add an attribute). However, using an attribute and environment
extension, as done in this file, has the following advantages:
  - If a theorem does not quite match the correct shape, the attribute handler can report
    the error immediately at the theorem declaration.
  - Recording the results just once avoids the need to linearly scan the whole environment
    (could get expensive) at each downstream usage point.
  - Requiring explicit opt-in prevents the possibility of accidental inclusions of unwanted theorems.
-/

open Lean Parser Elab Command

/-- An entry in the equational results or conjecture environment extension.
-/
inductive EntryVariant where
  | implication : Implication → EntryVariant
  | facts : Facts → EntryVariant
  /-- An equation that always holds. -/
  | unconditional : String → EntryVariant
deriving Lean.ToJson, Lean.FromJson, Inhabited

/-- An entry in the equational results environment extension -/
structure Entry where
  /-- Name of the declaration. -/
  name : Name
  /-- Name of the file where this declaration was found. -/
  filename : String
  /-- Line number of the declaration, if available -/
  line : Option Nat
  /-- Which kind of result is it? -/
  variant : EntryVariant
  /-- Is it proven? -/
  proven : Bool
deriving Lean.ToJson, Lean.FromJson, Inhabited

def Entry.toConjecture : Entry → Entry
  | .mk n f l v _ => ⟨n, f, l, v, false⟩

initialize equationalResultsExtension : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `equational_result
    addImportedFn := Array.concatMap id
    addEntryFn    := Array.push
  }

def Entry.keepCore (e : Entry) : Option Entry :=
  match e.variant with
  | .implication ⟨lhs, rhs, _⟩  =>
      if isCoreEquationName lhs && isCoreEquationName rhs
      then some e
      else none
  | .facts ⟨satisfied, refuted, finite⟩ =>
      let sat1 := satisfied.filterMap filterCoreEquationName
      let ref1 := refuted.filterMap filterCoreEquationName
      if sat1.isEmpty || ref1.isEmpty then none
      else some <| {e with variant := .facts {satisfied := sat1, refuted := ref1, finite := finite}}
  | .unconditional eq => if isCoreEquationName eq then some e else none

namespace Result

private def equationalResultHelpString : String :=
"tags theorems that provide implications or negated implications to the directed graph"

/-- Initialization of `equational_result` attribute -/
initialize equationalResultAttr : Unit ←
  registerBuiltinAttribute {
    name  := `equational_result
    descr := equationalResultHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx _attrKind => do
       let ctx ← read
       let filename := ctx.fileName
       let line := stx.getPos?.map λ pos => ctx.fileMap.toPosition pos |>.line
       discard <| Meta.MetaM.run do
       let mut is_conjecture := false
       let axioms ← Lean.collectAxioms declName
       for a in axioms do
         if a = `Conjecture.conjectureAx then
           is_conjecture := true
         else if not (a ∈ [``propext, ``Classical.choice, ``Quot.sound]) then
           throwError s!"declaration uses a prohibited axiom: {a}"

       let info ← getConstInfo declName
       let entry ← match info with
                   | .thmInfo  (val : TheoremVal) =>
                     if let some imp ← parseImplication val.type then
                       pure <| ⟨val.name, filename, line, .implication imp, true⟩
                     else if let some facts ← parseFacts val.type then
                       pure <| ⟨val.name, filename, line, .facts facts, true⟩
                     else if let some uncond ← parseUnconditionalEquation val.type then
                       pure <| ⟨val.name, filename, line, .unconditional uncond, true⟩
                     else
                       throwError "failed to match type of @[equational_result] theorem"
                   | _ => throwError "@[equational_result] is only allowed on theorems"

       let entry := if is_conjecture then entry.toConjecture else entry

       -- Add law theorem as well
       match entry.variant with
        | .implication imp =>
            let _ ← match info with
              | .thmInfo  (val : TheoremVal) =>
                 if !imp.finite then addLawImplicationThm val.type val.name
              | _ => pure ()
        | .unconditional _ =>
            let _ ← match info with
              | .thmInfo  (val : TheoremVal) =>
                 addLawUnconditionalThm val.type val.name
              | _ => pure ()
        | _ => pure ()

       modifyEnv fun env =>
         equationalResultsExtension.addEntry env entry
    erase := fun _declName =>
      throwError "can't remove `equational_result` attribute (not implemented yet)"
  }

/-- Returns the contents of the equational results environment extension.
-/
def extractEquationalResults {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return equationalResultsExtension.getState (← getEnv)

def extractTheorems {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return (equationalResultsExtension.getState (← getEnv)).filter (·.proven)

def extractConjectures {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return (equationalResultsExtension.getState (← getEnv)).filter (!·.proven)

/-- Prints the contents of the equational results environment extension.
-/
syntax (name := printEquationalResults) "#print_equational_results" : command

elab_rules : command
| `(command| #print_equational_results) => do
  let rs ← extractTheorems
  for ⟨name, _filename, _line, res, _⟩ in rs do
    match res with
    | .implication ⟨lhs, rhs, _⟩ => println! "{name}: {lhs} → {rhs}"
    | .facts ⟨satisfied, refuted, _⟩ => println! "{name}: {satisfied} // {refuted}"
    | .unconditional rhs => println! "{name}: {rhs} holds unconditionally"

end Result

namespace Conjecture

/--
Like `proof_wanted` from Batteries, but "leaks" a `@[equational_result]` attribute modifier,
marking it as a conjecture.
-/
@[command_parser]
def «conjecture» := leading_parser
  declModifiers false >> "conjecture" >> declId >> ppIndent declSig

-- Axiom used in conjectures.
axiom conjectureAx (p : Prop) : p

/-- Elaborates a `conjecture` declaration. The declaration is translated to an axiom during
elaboration, but it's then removed from the environment.
-/
@[command_elab «conjecture»]
def elabConjecture : CommandElab
  | `($mods:declModifiers conjecture $name $args* : $res) => do
    let maybe_entry ← withoutModifyingEnv do
      let original_length := (equationalResultsExtension.getState (← getEnv)).size

      elabDeclaration <| ← `(command| $mods:declModifiers
                                      theorem $name $args* : $res := Conjecture.conjectureAx _)

      -- If we add a new entry to the equational results list
      if original_length < (equationalResultsExtension.getState (← getEnv)).size then
        return some (equationalResultsExtension.getState (← getEnv)).back
      return none

    if let some entry := maybe_entry then
      modifyEnv fun env => -- then add it as a conjecture
        equationalResultsExtension.addEntry env entry.toConjecture
    pure ()
  | _ => throwUnsupportedSyntax

end Conjecture
