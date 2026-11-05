import equational_theories.Parastrophes.Equation1516ColumnCriterion
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# Common and Short do not characterize E1516's division image

This counterexample has 38 elements, but requires no multiplication table or
solver certificate. More generally take Z/19Z × V, where V is any nontrivial
abelian group of exponent two. The first coordinate is -2i+3j+1. In the
second coordinate, put d=j-i and use

* u+v if d=13;
* v if d is 4, 8, or 11;
* 0 otherwise.

Three successive products in Common have differences d, 2d+1, and 6d+4.
The last product is zero except possibly at d=0,7,11,17. The middle product
vanishes at 0,7,17; at 11 the last product is v+v=0. Hence the common map
is (i,u) ↦ (i+13,0). The two products in Short have differences 13 and 8,
so they preserve u and return (i,u). Every row nevertheless collapses the
two elements above its own first coordinate.

Thus the missing injectivity in the earlier two-identity proposal is false.
The single-equation catalogue question itself remains open.
-/
namespace Parastrophes.Eq1516CommonCounterexample
open Eq1516Image

variable {V : Type} [AddCommGroup V]

def fibre (d : ZMod 19) (u v : V) : V :=
  if d = 13 then u + v else if d = 4 ∨ d = 8 ∨ d = 11 then v else 0

@[implicit_reducible] def model : Magma (ZMod 19 × V) :=
  ⟨fun x y => (-2*x.1 + 3*y.1 + 1, fibre (y.1-x.1) x.2 y.2)⟩

private theorem fibre_cross (htwo : ∀ v : V, v + v = 0)
    (d : ZMod 19) (u v : V) :
    fibre (6*d+4) v (fibre (2*d+1) v (fibre d u v)) = 0 := by
  fin_cases d <;> simp +decide [fibre]
  change v + v = 0
  exact htwo v

/-- The common map discards the entire second coordinate. -/
theorem cross_formula (htwo : ∀ v : V, v + v = 0)
    (x y : ZMod 19 × V) : cross model x y = (x.1+13, 0) := by
  apply Prod.ext
  · change -2*y.1 + 3*(-2*y.1 + 3*(-2*x.1 + 3*y.1 + 1) + 1) + 1 = x.1+13
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  · change fibre ((-2*y.1 + 3*(-2*x.1 + 3*y.1 + 1) + 1) - y.1) y.2
      (fibre ((-2*x.1 + 3*y.1 + 1) - y.1) y.2
        (fibre (y.1-x.1) x.2 y.2)) = 0
    have h₁ : (-2*x.1 + 3*y.1 + 1) - y.1 = 2*(y.1-x.1)+1 := by ring
    have h₂ : (-2*y.1 + 3*(-2*x.1 + 3*y.1 + 1) + 1) - y.1 =
        6*(y.1-x.1)+4 := by ring
    rw [h₁, h₂]
    exact fibre_cross htwo _ _ _

theorem turn_formula (htwo : ∀ v : V, v + v = 0) (x : ZMod 19 × V) :
    turn model x = (x.1+13, 0) := cross_formula htwo x x

theorem common (htwo : ∀ v : V, v + v = 0) : Common (model (V := V)) := by
  intro x y
  rw [cross_formula htwo, turn_formula htwo]

theorem short (htwo : ∀ v : V, v + v = 0) : Short (model (V := V)) := by
  intro x y z
  rw [cross_formula htwo, cross_formula htwo]
  apply Prod.ext
  · change -2*(x.1+13) + 3*(-2*x.1+3*(x.1+13)+1)+1 = x.1
    ring_nf
    reduce_mod_char
  · change fibre ((-2*x.1+3*(x.1+13)+1)-(x.1+13)) 0
      (fibre ((x.1+13)-x.1) x.2 0) = x.2
    have h₁ : (x.1+13)-x.1 = (13 : ZMod 19) := by ring
    have h₂ : (-2*x.1+3*(x.1+13)+1)-(x.1+13) = (8 : ZMod 19) := by
      ring_nf
      reduce_mod_char
    rw [h₁, h₂]
    norm_num [fibre]

/-- No actual division operation has the row collision present here.
This conclusion does not need finiteness or the exponent-two assumption. -/
theorem not_image [Nontrivial V] : ¬ InImage Law1516 .left (model (V := V)) := by
  rintro ⟨M, _, hd⟩
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  have hi := (sideQuasigroup_of_division (division_symm hd)) (0, u)
  have he : model.op (0, u) (0, u) = model.op (0, u) (0, v) := by
    rfl
  exact huv (congrArg Prod.snd (hi.1 he))

/-- The finite member has 19·2=38 elements. -/
abbrev finiteModel : Magma (ZMod 19 × ZMod 2) := model

private theorem two : ∀ v : ZMod 2, v + v = 0 := by decide

theorem finite_common_short : Common finiteModel ∧ Short finiteModel :=
  ⟨common two, short two⟩

theorem finite_not_image : ¬ InImage Law1516 .left finiteModel := not_image

theorem finite_card : Fintype.card (ZMod 19 × ZMod 2) = 38 := by decide

/-! The idempotent-free quotient used to discover the construction. -/

@[implicit_reducible] def seed : Magma (ZMod 19) := ⟨fun x y => -2*x+3*y+1⟩

@[implicit_reducible] def seedSource : Magma (ZMod 19) := ⟨fun x y => 7*x+13*y+6⟩

theorem seedSource_law : @Equation1516 (ZMod 19) seedSource := by
  intro x y
  change x = 7*(7*y+13*y+6)+13*(7*x+13*(7*x+13*y+6)+6)+6
  ring_nf
  reduce_mod_char

theorem seed_division : IsDivision .left seedSource seed := by
  constructor <;> intro x y
  · change 7*x+13*(-2*x+3*y+1)+6 = y
    ring_nf
    reduce_mod_char
  · change -2*x+3*(7*x+13*y+6)+1 = y
    ring_nf
    reduce_mod_char

theorem seed_in_image : InImage Law1516 .left seed :=
  ⟨seedSource, (@Law1516.models_iff (ZMod 19) seedSource).mpr seedSource_law,
    seed_division⟩

theorem seed_no_idempotents (x : ZMod 19) : seed.op x x ≠ x := by
  intro h
  have he : (1 : ZMod 19) = 0 := by
    calc
      1 = seed.op x x - x := by change 1 = (-2*x+3*x+1)-x; ring
      _ = 0 := by rw [h, sub_self]
  exact (by decide : (1 : ZMod 19) ≠ 0) he

end Parastrophes.Eq1516CommonCounterexample
