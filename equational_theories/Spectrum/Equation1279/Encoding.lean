import equational_theories.Spectrum.Equation1279.Normalization

/-! The fixed diagonal and the justified first-row bounds for E1279. -/
namespace Spectrum.E1279.Encoding
open Std.Sat SmallOrders
open SmallOrders.Encoding (Atom p)
open E63.OrderTen.Encoding (all1)
variable {n : ℕ} [NeZero n]

def units (d : Fin n → Fin n) : CNF (Atom n) :=
  all1 fun x => ⟨#[[(p x x (d x),true)]]⟩

def rowBound (k : ℕ) : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + k < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty

abbrev toNat (F : CNF (Atom n)) : CNF ℕ := E1110.SquareEncoding.toNat F
end Spectrum.E1279.Encoding
