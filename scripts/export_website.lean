import equational_theories.Definability
import equational_theories.Spectrum
import Lean.PrivateName

/-! Export source locations and actual dependency status for the research explorers.
Run website_declarations.py first, then `lake env lean scripts/export_website.lean`.
Only named source declarations are exported, not compiler-generated helper theorems.
Pending spectrum declarations are claims, even though Lean accepts their placeholders.
-/
open Lean Elab Command

set_option maxHeartbeats 0

run_elab do
  let output := (← IO.getEnv "WEBSITE_DECLARATIONS").getD "/tmp/website-declarations.json"
  let input := (← IO.getEnv "WEBSITE_DECLARATION_REQUESTS").getD "/tmp/website-declaration-requests.json"
  let data ← IO.FS.readFile input
  let requests ← ofExcept ((Json.parse data).bind Json.getArr?)
  let mut byFile : Std.HashMap String (NameMap Json) := {}
  for request in requests do
    let file ← ofExcept ((request.getObjVal? "file").bind Json.getStr?)
    let name ← ofExcept ((request.getObjVal? "name").bind Json.getStr?)
    byFile := byFile.insert file ((byFile[file]?.getD {}).insert name.toName request)
  let env ← getEnv
  let mut cache : NameMap Spectrum.Status.Summary := {}
  let mut records : Array Json := #[]
  -- Enumerating individual modules avoids traversing the entire Mathlib environment.
  for idx in [:env.header.moduleData.size] do
    let mod := env.header.moduleNames[idx]!.toString
    let file := mod.replace "." "/" ++ ".lean"
    if let some wanted := byFile[file]? then
      for ci in env.header.moduleData[idx]!.constants do
        unless (ci matches .thmInfo ..) do continue
        if let some request := wanted.find? (privateToUserName ci.name) then
          let name := ci.name
          let (summary, next) := ((Spectrum.Status.analyse name).run env).run cache
          cache := next
          -- Definability also uses native_decide and the repository's nativeDecideFin!. Spectrum has its own stricter
          -- explicit native-attribute policy, checked by Status.analyse.
          let bad := if mod.startsWith "equational_theories.Definability" then
            summary.bad.filter fun n =>
              !((n.toString.splitOn "._native.native_decide.ax_").length > 1 ||
                (n.toString.splitOn "._native.bv_decide.ax_").length > 1 ||
                (n.toString.splitOn "._native.nativeDecideFin.ax_").length > 1)
            else summary.bad
          let evidence := if !bad.isEmpty then "UNVERIFIED"
            else if summary.evidence env == .noteGap then "NOTE_GAP"
            else if !summary.pending.isEmpty then "PROOF_AVAILABLE" else "PROVED"
          let line ← ofExcept ((request.getObjVal? "line").bind Json.getNat?)
          let pending := summary.pending.map fun n =>
            let info := (Spectrum.Status.pendingExtension.getState env).find? n |>.getD default
            Json.mkObj [("name", toJson n.toString), ("source", toJson info.source),
              ("missing", toJson info.missing)]
          records := records.push <| Json.mkObj [
            ("name", toJson name.toString), ("file", toJson file),
            ("line", toJson line), ("status", toJson evidence),
            ("pending", toJson pending), ("bad", toJson (bad.map Name.toString))]
      if records.size % 10000 < 100 then
        IO.println s!"Audited {records.size} source declarations ({mod})"
  IO.FS.writeFile output (toJson records).compress
  IO.println s!"Exported {records.size} declaration records to {output}"
