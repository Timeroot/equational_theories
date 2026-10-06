import equational_theories.Spectrum.Equation467.OrderSixteen.CertificateOptions
open Spectrum.E467.OrderSixteen Spectrum.E467.OrderSixteen.Encoding

def main (args : List String) : IO Unit := do
  let file := args.headD ".cache/e467-sixteen-cnf.cnf"
  for k in [:112] do
    let cnf := natOptimized useRotation ⟨k%112, Nat.mod_lt _ (by decide)⟩
    let stream ← IO.FS.Handle.mk file .write
    stream.putStrLn s!"p cnf 4096 {cnf.clauses.size}"
    for clause in cnf.clauses do
      stream.putStrLn (String.intercalate " " (clause.map fun (v,b) => (if b then "" else "-") ++ toString (v+1)) ++ " 0")
    stream.flush
    let result ← IO.Process.output {cmd := "sha256sum", args := #[file]}
    IO.println s!"{k} {result.stdout.trimAscii}"
  IO.FS.removeFile file
