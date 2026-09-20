import equational_theories.Definability.LeftProjectionCounting
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by left translations and a group projection. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.LeftProjectionS3By2
def A := Fin 6
instance : Fintype A := inferInstanceAs (Fintype (Fin 6))
instance : DecidableEq A := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat A n := inferInstanceAs (OfNat (Fin 6) n)
instance : Inhabited A := ⟨0⟩
def baseData : Array (Array A) := #[#[0, 1, 2, 3, 4, 5], #[1, 0, 4, 5, 2, 3], #[2, 3, 0, 1, 5, 4], #[3, 2, 5, 4, 0, 1], #[4, 5, 1, 0, 3, 2], #[5, 4, 3, 2, 1, 0]]
def inverseData : Array A := #[0, 1, 2, 4, 3, 5]
instance : Add A := ⟨fun x y => (baseData.getD x.val #[]).getD y.val 0⟩
instance : Zero A := ⟨0⟩
instance : Neg A := ⟨fun x => inverseData.getD x.val 0⟩
instance : AddGroup A := AddGroup.ofLeftAxioms (by native_decide) (by native_decide) (by native_decide)
abbrev B := ZMod 2
abbrev Params := Magma.ProjectionFamily.Params A B
@[implicit_reducible] def model (p : Params) : Magma (A × B) := Magma.LeftProjectionFamily.fam p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (Equiv.addLeft a) :=
  Magma.LeftProjectionFamily.family_generators p (.inl a)
theorem move_zero : ∀ a : A × B, Equiv.addLeft a 0 = a := by intro a; exact add_zero a

private def law418 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 2)))))⟩
private theorem count418 : Fintype.card {p : Params // PointTest (0 : A × B) (model p) law418} = 3615 := by native_decide

private def law621 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Leaf 2))))⟩
private theorem count621 : Fintype.card {p : Params // PointTest (0 : A × B) (model p) law621} = 3567 := by native_decide

end Magma.LeftProjectionS3By2

open Magma.LeftProjectionS3By2

theorem Equation621_not_termStructuralFromFin_Equation418_leftProjectionS3By2 : ¬ Law621.TermStructuralFromFin Law418 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.LeftProjectionFamily.gen (A := A) (B := B))
    model Magma.LeftProjectionFamily.family_injective Magma.LeftProjectionFamily.coverage
    Magma.LeftProjectionFamily.family_generators
    (fun p => PointTest (0 : A × B) (model p) law418)
    (fun p => PointTest (0 : A × B) (model p) law621)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count418, count621]
    decide

/-- info: 'Equation621_not_termStructuralFromFin_Equation418_leftProjectionS3By2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 instAddGroupA._native.native_decide.ax_1,
 instAddGroupA._native.native_decide.ax_2,
 instAddGroupA._native.native_decide.ax_3,
 count418._native.native_decide.ax_1_1,
 count621._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation621_not_termStructuralFromFin_Equation418_leftProjectionS3By2

