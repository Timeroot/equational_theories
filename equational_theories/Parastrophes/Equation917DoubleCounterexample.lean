import equational_theories.Parastrophes.Equation917DoubleCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# The last 34-operation double-bridge candidate is false

The operation `x*y=43*x+209*y+1` on Z/251Z satisfies candidate 5, but
`x*c(x)=x+211`, so it fails the image basis. The auxiliary maps have no fixed
points: g(x)=x+211 and f(x)=x+37. Thus the fixed-point hypothesis in the
earlier conditional converse cannot be removed for this candidate.

The exceptional prime was found by eliminating the affine coefficient b:
the cubic b³-b+1 and 10b²-16b+11 have resultant 251. Their common
root modulo 251 is b=209. The proof below is entirely symbolic and checks
no six-dimensional table.
-/
namespace Parastrophes.Eq917Image.DoubleCounterexample
open DoubleCandidate

@[implicit_reducible] def model : Magma (ZMod 251) :=
  ⟨fun x y => 43*x + 209*y + 1⟩

theorem core_model (x : ZMod 251) : core model x = x+246 := by
  change 43*(43*x+209*(43*x+209*x+1)+1)+209*x+1 = x+246
  ring_nf
  reduce_mod_char

theorem F_model (x z : ZMod 251) : SplitCandidate.F model x z = x+211 := by
  change 43*z+209*(43*(core model x)+209*(43*x+209*z+1)+1)+1 = x+211
  rw [core_model]
  ring_nf
  reduce_mod_char

theorem U_model (x : ZMod 251) : U model x = x+211 := by
  change 43*x+209*(core model x)+1 = x+211
  rw [core_model]
  ring_nf
  reduce_mod_char

theorem B1_model (x z w : ZMod 251) : B1 model x z w = x+248 := by
  change 43*(SplitCandidate.F model z w)+209*(43*(core model x)+209*(43*x+209*z+1)+1)+1 = x+248
  rw [F_model, core_model]
  ring_nf
  reduce_mod_char

theorem B2_model (x v t : ZMod 251) : B2 model x v t = x+174 := by
  change 43*v+209*(43*(core model x)+209*(43*x+209*(SplitCandidate.F model v t)+1)+1)+1 = x+174
  rw [F_model, core_model]
  ring_nf
  reduce_mod_char

theorem K_model (x z w v t : ZMod 251) : K model x z w v t = x+112 := by
  unfold K
  rw [B1_model, B2_model, U_model]
  change 43*(43*x+209*(43*(x+174)+209*(x+248)+1)+1)+209*(x+211)+1 = x+112
  ring_nf
  reduce_mod_char

theorem candidate_holds : Identity model := by
  intro x y z w v t
  rw [K_model]
  change x = 43*y+209*(43*(x+112)+209*(43*x+209*y+1)+1)+1
  ring_nf
  reduce_mod_char

theorem not_basis : ¬ Basis model := by
  intro h
  have he : (0 : ZMod 251) = U model 0 := h.1 0
  rw [U_model] at he
  exact (by decide : (0 : ZMod 251) ≠ 0+211) he

theorem not_image : ¬ InImage Law917 .left model :=
  fun h => not_basis ((characterizes_fin model).2 h)

end Parastrophes.Eq917Image.DoubleCounterexample
