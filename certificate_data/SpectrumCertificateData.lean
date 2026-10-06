import Lean
import SpectrumCertificateData.Replay

/-! Embed a compressed binary certificate through an ASCII base64 literal.
The decoder is an ordinary pure Lean function. Decompression only supplies
literal data during elaboration; the proof checker subsequently validates it.
Binary LRAT avoids embedding the much larger decimal-text proof. -/
namespace Spectrum.CertificateData

@[inline] private def digit (c : UInt8) : Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then n-65
  else if 97 ≤ n ∧ n ≤ 122 then n-71
  else if 48 ≤ n ∧ n ≤ 57 then n+4
  else if n = 43 then 62 else 63

/-- Decode the embedded ASCII data. Bad input cannot bypass the certificate checker. -/
def decode (input : String) : ByteArray := Id.run do
  let bytes := input.toUTF8
  let mut out := ByteArray.emptyWithCapacity (3*(bytes.size/4))
  for k in [:bytes.size/4] do
    let i := 4*k
    let a := digit bytes[i]!
    let b := digit bytes[i+1]!
    let c := digit bytes[i+2]!
    let d := digit bytes[i+3]!
    out := out.push (4*a+b/16).toUInt8
    if bytes[i+2]! != 61 then out := out.push (16*(b%16)+c/4).toUInt8
    if bytes[i+3]! != 61 then out := out.push (64*(c%4)+d).toUInt8
  return out

open Lean Elab Term in
private def includeCompressed (path : TSyntax `str) (xz : Bool) : TermElabM Expr := do
  let ctx ← readThe Lean.Core.Context
  let some dir := (System.FilePath.mk ctx.fileName).parent
    | throwError "cannot compute source directory"
  let input := dir / path.getString
  -- Fixed shell program; the file name is passed as an argument, never interpolated.
  let result ← IO.Process.output {
    cmd := "bash"
    args := #["-o", "pipefail", "-c",
      if xz then "xz -dc -- \"$1\" | base64 -w0" else "gzip -dc -- \"$1\" | base64 -w0",
      "include_compressed_binary", input.toString]
  }
  if result.exitCode != 0 then throwError "certificate read failed for {input}: {result.stderr}"
  return mkApp (mkConst ``decode) (mkStrLit result.stdout)

open Lean Elab Term in
elab "include_binary_gzip " path:str : term => includeCompressed path false

open Lean Elab Term in
elab "include_binary_xz " path:str : term => includeCompressed path true

end Spectrum.CertificateData
