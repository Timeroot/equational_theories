import equational_theories.Parastrophes.Equation917DoubleUnitCandidate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# The single-U comparison fails in characteristic eleven

Deleting U from the w input in the twenty-operation candidate gives a
sixteen-operation identity. The affine quasigroup 7x+5y+1 over Z/11 satisfies
it but has U(0)≠0, so is not an E917 left-division image. This also explains
why a Groebner-basis computation in characteristic zero is insufficient:
the relevant integral resultant is eleven, not one. The double-U candidate
excludes this model; its companion affine proof has Bezout constant one.
-/
namespace Parastrophes.Eq917Image.SingleUnitCounterexample
open SandwichCandidate (U H)

def Compared {A : Type} (D : Magma A) : Prop := ∀ x y z w v,
  x = D.op (D.op (D.op w (D.op (U D z) y)) v)
    (H D x (D.op (D.op w (D.op z y)) v))

@[implicit_reducible] def bad : Magma (ZMod 11) := ⟨fun x y => 7*x+5*y+1⟩

theorem bad_compared : Compared bad := by
  intro x y z w v
  dsimp [bad, Magma.op, U, H, core]
  ring_nf
  reduce_mod_char

theorem bad_not_image : ¬ InImage Law917 .left bad := by
  intro h
  have hb := (characterizes_fin bad).mpr h
  exact (by decide : U bad 0 ≠ 0) (hb.1 0).symm

theorem bad_not_double : ¬ DoubleUnitCandidate.Identity bad := by
  intro h
  have he := h 0 0 0 0 0
  exact (by decide : ¬ ((0 : ZMod 11) =
    bad.op (bad.op (bad.op (U bad 0) (bad.op (U bad 0) 0)) 0)
      (H bad 0 (bad.op (bad.op 0 (bad.op 0 0)) 0)))) he

/-- Adding U to all three inner inputs is also insufficient. The obstruction
is visible over Z/25 although it vanishes in its reduction modulo five. -/
def TripleCompared {A : Type} (D : Magma A) : Prop := ∀ x y z w v,
  x = D.op (D.op (D.op (U D w) (D.op (U D z) (U D y))) v)
    (H D x (D.op (D.op w (D.op z y)) v))

@[implicit_reducible] def bad25 : Magma (ZMod 25) := ⟨fun x y => 23*x+3*y+1⟩

theorem bad25_triple_compared : TripleCompared bad25 := by
  intro x y z w v
  dsimp [bad25, Magma.op, U, H, core]
  ring_nf
  reduce_mod_char

theorem bad25_not_image : ¬ InImage Law917 .left bad25 := by
  intro h
  have hb := (characterizes_fin bad25).mpr h
  exact (by decide : U bad25 0 ≠ 0) (hb.1 0).symm

end Parastrophes.Eq917Image.SingleUnitCounterexample
