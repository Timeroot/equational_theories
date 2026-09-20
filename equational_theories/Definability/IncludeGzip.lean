import Lean

/-!
# Embed a gzip-compressed textual certificate

Decompression runs during elaboration and produces a string literal. The kernel sees that
literal, and certificate checkers still prove their conclusions from its contents. The
external `gzip` program is not part of a theorem's trusted proof computation.

Generated certificate modules record a content hash so changing their compressed input
also changes their generated source and invalidates the ordinary Lake build cache.
-/

open Lean Elab Term in
elab "include_gzip_str " path:str : term => do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of {srcPath}"
  let input := srcDir / path.getString
  let output ← IO.Process.output {cmd := "gzip", args := #["-dc", "--", input.toString]}
  if output.exitCode != 0 then
    throwError "gzip failed for {input}: {output.stderr}"
  return Lean.mkStrLit output.stdout
