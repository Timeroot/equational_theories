import equational_theories.Spectrum.Equation63.IdempotentSeeds
import equational_theories.Spectrum.Equation63.FieldDesign
import equational_theories.Spectrum.Status

/-! A new idempotent E63 model of order 31, discovered in the homogeneous
E1516 search. Only two lists of 31 values are needed, not a 31-by-31 table.
The Lean kernel checks every law instance and every diagonal entry.
The order-255 consequence uses the existing field transversal design. -/
namespace Spectrum.E63

private def inverse31 : Fin 31 → Fin 31 := ![0, 1, 16, 21, 8, 25, 26, 9, 4, 7, 28, 17, 13, 12, 20, 29, 2, 11, 19, 18, 14, 3, 24, 27, 22, 5, 6, 23, 10, 15, 30]

private def profile31 : Fin 31 → Fin 31 := ![30, 1, 28, 29, 13, 6, 26, 3, 20, 4, 8, 23, 16, 9, 15, 19, 17, 12, 27, 14, 10, 11, 18, 21, 2, 0, 5, 22, 24, 7, 25]

/-- Over F31, `p(0,y)=5y` and `p(x,y)=x h(y/x)` for nonzero x. -/
def homogeneousOp31 (x y : Fin 31) : Fin 31 :=
  if x = 0 then ⟨(5*y.val) % 31, Nat.mod_lt _ (by decide)⟩
  else
    let i : Fin 31 := ⟨(y.val*(inverse31 x).val) % 31, Nat.mod_lt _ (by decide)⟩
    ⟨(x.val*(profile31 i).val) % 31, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem homogeneous31_law : Lawful homogeneousOp31 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem homogeneous31_idem : Idem homogeneousOp31 := by decide +kernel

theorem idem31 : Model (Fin 31) true :=
  ⟨homogeneousOp31, homogeneous31_law, fun _ => homogeneous31_idem⟩

/-- The new seed supplies the previously missing truncated group of order 31
in the field design of order 32: `7*32+31=255`. -/
theorem idem255 : Model (Fin 255) true :=
  (prime_power_td (p := 2) (e := 5) (by decide) (by decide)
    (by decide)).idempotent_models (by decide) idem32 idem31

spectrum_assert idem31 complete
spectrum_assert idem255 complete

/-- info: 'Spectrum.E63.idem31' depends on axioms: [propext] -/
#guard_msgs in
#print axioms idem31
/-- info: 'Spectrum.E63.idem255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idem255
end Spectrum.E63
