import equational_theories.Spectrum

/-! The website's individual model certificates are discovered by name. Check
that each name actually has the claimed HasModel type before publishing it. -/
open Lean Meta Elab Command in
run_elab do
  let text ← IO.FS.readFile "home_page/research/data/spectrum.json"
  let data ← ofExcept (Json.parse text)
  let records ← ofExcept ((data.getObjVal? "records").bind Json.getArr?)
  let mut count : Nat := 0
  for record in records do
    let i ← ofExcept ((record.getObjVal? "equation").bind Json.getNat?)
    let witnesses ← ofExcept ((record.getObjVal? "witnesses").bind Json.getArr?)
    for witness in witnesses do
      let order ← ofExcept ((witness.getObjVal? "order").bind Json.getNat?)
      let name ← ofExcept ((witness.getObjVal? "theorem").bind Json.getStr?)
      let expected ← mkAppM ``Law.MagmaLaw.HasModel
        #[mkConst (.mkSimple s!"Law{i}"), mkNatLit order]
      unless ← isDefEq (← getConstInfo name.toName).type expected do
        throwError "Wrong individual model certificate type: {name}, E{i}, order {order}"
      count := count + 1
  logInfo m!"Verified the types of {count} individual website model certificates."
