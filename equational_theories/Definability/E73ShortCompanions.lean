import equational_theories.Definability.CloneTraps
import equational_theories.Definability.E63Family
import equational_theories.Spectrum.Status
import Mathlib.Data.ZMod.Basic
import equational_theories.ManuallyProved.Equation73

/-!
# Four short E8 companions of E73, and three recovery obstructions

All four six-leaf terms satisfy E8 on every E73 magma. Three cannot
uniformly recover the source: the first is a projection on an eight-point
E125 magma, and the second and fourth are projections on a five-point one.
Every term of a projection ignores an argument, but the source depends
on both. The source laws and projection identities use small kernel checks.

The third companion agrees with the usual left division on E125 and
recovers E125 there by two products. Its general E73 recovery remains open.
These concern particular defining terms, not separation of the E73 and E8
classes; their unrestricted term-structural arrow remains unknown.
-/

namespace E73ShortCompanions

@[reducible] def first {G : Type} (M : Magma G) : Magma G :=
  ⟨fun x y => M.op x (M.op x (M.op x (M.op y (M.op x y))))⟩
@[reducible] def second {G : Type} (M : Magma G) : Magma G :=
  ⟨fun x y => M.op x (M.op x (M.op x (M.op y (M.op y x))))⟩
@[reducible] def third {G : Type} (M : Magma G) : Magma G :=
  ⟨fun x y => M.op y (M.op (M.op x (M.op x (M.op x y))) x)⟩
@[reducible] def fourth {G : Type} (M : Magma G) : Magma G :=
  ⟨fun x y => M.op (M.op x (M.op x (M.op x y))) (M.op y x)⟩

lemma first_law {G : Type} [M : Magma G] (h : Equation73 G) : @Equation8 G (first M) := by
  intro x
  grind

lemma second_law {G : Type} [M : Magma G] (h : Equation73 G) : @Equation8 G (second M) := by
  intro x
  grind

lemma third_law {G : Type} [M : Magma G] (h : Equation73 G) : @Equation8 G (third M) := by
  intro x
  grind

lemma fourth_law {G : Type} [M : Magma G] (h : Equation73 G) : @Equation8 G (fourth M) := by
  intro x
  grind

lemma third_on125 {G : Type} [M : Magma G] (h : Equation125 G) (x y : G) :
    (third M).op x y = (y ◇ x) ◇ y := by
  change y ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ x) = _
  rw [E63Family.rotate_125 h]
  apply E63Family.left_injective_125 h y
  exact (E63Family.equation73_of_125 h x y).symm.trans (h x y)

lemma third_recover125 {G : Type} [M : Magma G] (h : Equation125 G) (x y : G) :
    (third M).op ((third M).op x y) y = x ◇ y := by
  rw [third_on125 h, third_on125 h]
  exact congrArg (fun z => z ◇ y) (h x y).symm

@[reducible] def five : Magma (ZMod 5) := ⟨fun x y => 4*x+2*y⟩
lemma five_law : @Equation125 (ZMod 5) five := by decide
lemma second_five (x y : ZMod 5) : (second five).op x y = y := by revert x y; decide
lemma fourth_five (x y : ZMod 5) : (fourth five).op x y = x := by revert x y; decide
lemma five_essential : ¬ Magma.IgnoreArg five.op := by decide

abbrev V := Fin 3 → ZMod 2
def a (x : V) : V := ![x 2, x 0+x 2, x 1]
@[reducible] def eight : Magma V := ⟨fun x y i => a x i+y i-a y i⟩
lemma eight_law : @Equation125 V eight := by decide
lemma first_eight (x y : V) : (first eight).op x y = y := by revert x y; decide
lemma eight_essential : ¬ Magma.IgnoreArg eight.op := by decide

lemma no_recovery {G : Type} {M N : Magma G} (hM : ¬ Magma.IgnoreArg M.op)
    (hN : Magma.IgnoreArg N.op) :
    ¬ @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ M.FinArityOp := by
  intro h
  exact hM (hN.isCloneInvariant.of_termDefinable h)

lemma first_no_uniform_recovery :
    ¬ @Set.TermDefinable _ ∅ MagmaLanguage (first eight).FOStructure _ eight.FinArityOp :=
  no_recovery eight_essential ⟨true, fun _ _ _ => by rw [first_eight,first_eight]⟩
lemma second_no_uniform_recovery :
    ¬ @Set.TermDefinable _ ∅ MagmaLanguage (second five).FOStructure _ five.FinArityOp :=
  no_recovery five_essential ⟨true, fun _ _ _ => by rw [second_five,second_five]⟩
lemma fourth_no_uniform_recovery :
    ¬ @Set.TermDefinable _ ∅ MagmaLanguage (fourth five).FOStructure _ five.FinArityOp :=
  no_recovery five_essential ⟨false, fun _ _ _ => by rw [fourth_five,fourth_five]⟩

namespace Infinite
open Eq73.Greedy
abbrev G := FreeGroup ℕ
private abbrev g (n : ℕ) : G := FreeGroup.of n

def seed : List (G × G) := E0List ++
  [((g 2)⁻¹,g 3),(g 3,(g 2)⁻¹),((g 3)⁻¹,g 4),(g 4*g 3*g 2,g 5)]
noncomputable def extension : Extension := ⟨fromList seed, fromList_ok⟩
@[reducible] noncomputable def model : Magma G := ⟨op extension⟩
lemma law : @Equation73 G model := eq73 extension

lemma eval_seed (x y : G) (h : (x,y) ∈ seed) : f extension x = y :=
  fromList_eval rfl x y h

lemma recovery_fails :
    (third model).op ((third model).op 1 1) 1 ≠ model.op 1 1 := by
  have h1 := eval_seed 1 (g 1) (by decide)
  have h2 := eval_seed (g 1) (g 2) (by decide)
  have h3 := eval_seed (g 2) 1 (by decide)
  have h4 := eval_seed ((g 2)⁻¹) (g 3) (by decide)
  have h5 := eval_seed (g 3) ((g 2)⁻¹) (by decide)
  have h6 := eval_seed ((g 3)⁻¹) (g 4) (by decide)
  have h7 := eval_seed (g 4*(g 3*g 2)) (g 5) (by decide)
  simp only [Magma.op,op,inv_one,mul_one,one_mul,h1,h2,h3,h4,h5,h6,
    mul_inv_rev,mul_assoc,mul_inv_cancel,mul_inv_cancel_left,h7]
  decide

end Infinite

end E73ShortCompanions

spectrum_assert E73ShortCompanions.first_law complete
spectrum_assert E73ShortCompanions.second_law complete
spectrum_assert E73ShortCompanions.third_law complete
spectrum_assert E73ShortCompanions.fourth_law complete
spectrum_assert E73ShortCompanions.five_law complete
spectrum_assert E73ShortCompanions.eight_law complete
spectrum_assert E73ShortCompanions.first_no_uniform_recovery complete
spectrum_assert E73ShortCompanions.second_no_uniform_recovery complete
spectrum_assert E73ShortCompanions.fourth_no_uniform_recovery complete
spectrum_assert E73ShortCompanions.third_on125 complete
spectrum_assert E73ShortCompanions.third_recover125 complete
spectrum_assert E73ShortCompanions.Infinite.law complete
spectrum_assert E73ShortCompanions.Infinite.recovery_fails complete
