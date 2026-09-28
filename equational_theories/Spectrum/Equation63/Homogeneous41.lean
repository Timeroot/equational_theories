import equational_theories.Spectrum.Equation63.IdempotentConstructions
import equational_theories.Spectrum.Status

/-! An idempotent E63 model of order41. The Lean kernel checks the compact
homogeneous profile independently of the CP-SAT search that found it. -/
namespace Spectrum.E63

private def inverse41 : Fin 41 → Fin 41 := ![0, 1, 21, 14, 31, 33, 7, 6, 36, 32, 37, 15, 24, 19, 3, 11, 18, 29, 16, 13, 39, 2, 28, 25, 12, 23, 30, 38, 22, 17, 26, 4, 9, 5, 35, 34, 8, 10, 27, 20, 40]

private def profile41 : Fin 41 → Fin 41 := ![31, 1, 29, 14, 37, 24, 11, 5, 15, 3, 18, 21, 39, 8, 9, 13, 4, 36, 40, 12, 30, 6, 2, 10, 7, 23, 33, 38, 26, 22, 35, 16, 27, 28, 17, 20, 34, 0, 32, 19, 25]

/-- Over F41, `p(0,y)=18y` and `p(x,y)=x h(y/x)` for nonzero x. -/
def homogeneousOp41 (x y : Fin 41) : Fin 41 :=
  if x = 0 then ⟨(18*y.val) % 41, Nat.mod_lt _ (by decide)⟩
  else
    let i : Fin 41 := ⟨(y.val*(inverse41 x).val) % 41, Nat.mod_lt _ (by decide)⟩
    ⟨(x.val*(profile41 i).val) % 41, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem homogeneous41_law : Lawful homogeneousOp41 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem homogeneous41_idem : Idem homogeneousOp41 := by decide +kernel

theorem idem41 : Model (Fin 41) true :=
  ⟨homogeneousOp41, homogeneous41_law, fun _ => homogeneous41_idem⟩

spectrum_assert idem41 complete
/-- info: 'Spectrum.E63.idem41' depends on axioms: [propext] -/
#guard_msgs in
#print axioms idem41
end Spectrum.E63
