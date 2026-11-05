import equational_theories.Parastrophes.Equation917SplitCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# An affine counterexample to the 22-operation E917 compression

On Z/59Z, put `x*y = 43*x + 17*y + 1`. Then the candidate's named
maps are `c(x)=x+8`, `F(x,z)=x+19`, `B(x,z,w)=x+10`, and
`K(x,z,w)=x+20`. Substituting K in the proposed identity gives x.
But `x*c(x)=x+19`, so the required unit identity fails.

These are polynomial calculations over Z/59Z; no table of 59^4 assignments
is enumerated. The counterexample rejects this particular compression, not
the existence of another single equation for the division image.
-/
namespace Parastrophes.Eq917Image.SplitCounterexample

@[implicit_reducible] def model : Magma (ZMod 59) :=
  ⟨fun x y => 43*x + 17*y + 1⟩

theorem core_model (x : ZMod 59) : core model x = x + 8 := by
  change 43*(43*x + 17*(43*x + 17*x + 1) + 1) + 17*x + 1 = x + 8
  ring_nf
  reduce_mod_char

theorem F_model (x z : ZMod 59) : SplitCandidate.F model x z = x + 19 := by
  change 43*z + 17*(43*(core model x) + 17*(43*x+17*z+1)+1)+1 = x+19
  rw [core_model]
  ring_nf
  reduce_mod_char

theorem B_model (x z w : ZMod 59) : SplitCandidate.B model x z w = x + 10 := by
  change 43*(SplitCandidate.F model z w) + 17*(43*(core model x) + 17*(43*x+17*z+1)+1)+1 = x+10
  rw [F_model, core_model]
  ring_nf
  reduce_mod_char

theorem K_model (x z w : ZMod 59) : SplitCandidate.K model x z w = x + 20 := by
  change 43*(43*(43*(SplitCandidate.B model x z w)+17*(core model x)+1)+17*(43*x+17*x+1)+1)+17*x+1 = x+20
  rw [B_model, core_model]
  ring_nf
  reduce_mod_char

theorem candidate_holds : SplitCandidate.Identity model := by
  intro x y z w
  rw [K_model]
  change x = 43*y + 17*(43*(x+20) + 17*(43*x + 17*y + 1) + 1) + 1
  ring_nf
  reduce_mod_char

theorem not_basis : ¬ Basis model := by
  intro h
  have hu := h.1 (0 : ZMod 59)
  change (0 : ZMod 59) = model.op 0 (core model 0) at hu
  rw [core_model] at hu
  exact (by decide : (0 : ZMod 59) ≠ 43*0+17*8+1) hu

theorem not_image : ¬ InImage Law917 .left model :=
  fun h => not_basis ((characterizes_fin model).2 h)

/- The remaining variant moves the putative unit to the last argument:
   K8(x,z,w) = (B(x,z,w)*(x*x))*(x*c(x)).
It survives prime-field affine tests, but fails over F8. In the table below,
the entries 0,...,7 encode polynomials of degree at most two in b as binary
digits, with b^3=b+1. The operation is (b+1)*x+b*y+1. -/

def K8 {G : Type} (M : Magma G) (x z w : G) : G :=
  M.op (M.op (SplitCandidate.B M x z w) (M.op x x)) (M.op x (core M x))

def Identity8 {G : Type} (M : Magma G) : Prop :=
  ∀ x y z w, x = M.op y (M.op (K8 M x z w) (M.op x y))

@[implicit_reducible] def model8 : Magma (Fin 8) := ⟨fun x y =>
  (![
    ![1,3,5,7,2,0,6,4], ![2,0,6,4,1,3,5,7],
    ![7,5,3,1,4,6,0,2], ![4,6,0,2,7,5,3,1],
    ![6,4,2,0,5,7,1,3], ![5,7,1,3,6,4,2,0],
    ![0,2,4,6,3,1,7,5], ![3,1,7,5,0,2,4,6]] :
    Fin 8 → Fin 8 → Fin 8) x y⟩

/-- Check the inner bridge once (512 triples), then only 64 outer pairs.
This avoids expanding the long identity on all 4096 quadruples. -/
theorem candidate8_holds : Identity8 model8 := by
  have hk : ∀ x z w : Fin 8, K8 model8 x z w = K8 model8 x 0 0 := by decide
  have ho : ∀ x y : Fin 8,
      x = model8.op y (model8.op (K8 model8 x 0 0) (model8.op x y)) := by decide
  intro x y z w
  rw [hk]
  exact ho x y

theorem not_basis8 : ¬ Basis model8 := by
  intro h
  exact (by decide : (0 : Fin 8) ≠ model8.op 0 (core model8 0)) (h.1 0)

theorem not_image8 : ¬ InImage Law917 .left model8 :=
  fun h => not_basis8 ((characterizes_fin model8).2 h)

end Parastrophes.Eq917Image.SplitCounterexample
