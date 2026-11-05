import equational_theories.Parastrophes.Equation883RightImage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Affine extensions of E2744 and a failed E883 recovery term

E2744 is the dual of E883. An extension of a base B has multiplication
`(i,u)*(j,v) = (B(i,j), a*u+b*v+c(i,j))`. The source law reduces to two
scalar coefficient equations and one offset equation for each pair in B.
Thus iterating extensions requires checks on their bases, not on all pairs
in their larger carriers.

The example below extends a four-element source by F7, then extends the
result by F2. Its actual left division refutes the seventeen-operation
square-recovery candidate from 4 November. This is a refutation of that
specific term; it does not answer the single-equation image question.
-/
namespace Parastrophes.Eq883Extensions

@[implicit_reducible] def extension {B R : Type} [CommRing R]
    (M : Magma B) (a b : R) (c : B → B → R) : Magma (B × R) :=
  ⟨fun x y => (M.op x.1 y.1, a*x.2+b*y.2+c x.1 y.1)⟩

theorem extension_law {B R : Type} [CommRing R]
    (M : Magma B) (h : @Equation2744 B M) (a b : R) (c : B → B → R)
    (ha : a*b^2=1) (hb : a^3+2*a^2*b+b=0)
    (hc : ∀ x y, a^2*c y y + a*b*c y x + a*c (M.op y y) (M.op y x) +
      c (M.op (M.op y y) (M.op y x)) y = 0) :
    @Equation2744 (B × R) (extension M a b c) := by
  intro x y
  apply Prod.ext
  · exact h x.1 y.1
  · change x.2 = a*(a*(a*y.2+b*y.2+c y.1 y.1)+
        b*(a*y.2+b*x.2+c y.1 x.1)+c (M.op y.1 y.1) (M.op y.1 x.1))+
        b*y.2+c (M.op (M.op y.1 y.1) (M.op y.1 x.1)) y.1
    linear_combination -x.2*ha-y.2*hb-hc x.1 y.1

@[implicit_reducible] def divided {B R : Type} [CommRing R]
    (D : Magma B) (a bi : R) (c : B → B → R) : Magma (B × R) :=
  ⟨fun x y => (D.op x.1 y.1, bi*(y.2-a*x.2-c x.1 (D.op x.1 y.1)))⟩

theorem extension_division {B R : Type} [CommRing R] (M D : Magma B)
    (hd : IsDivision .left M D) (a b bi : R) (hi : b*bi=1) (c : B → B → R) :
    IsDivision .left (extension M a b c) (divided D a bi c) := by
  constructor <;> intro x y <;> apply Prod.ext
  · exact hd.1 x.1 y.1
  · change a*x.2+b*(bi*(y.2-a*x.2-c x.1 (D.op x.1 y.1)))+
      c x.1 (D.op x.1 y.1)=y.2
    linear_combination (y.2-a*x.2-c x.1 (D.op x.1 y.1))*hi
  · exact hd.2 x.1 y.1
  · change bi*((a*x.2+b*y.2+c x.1 y.1)-a*x.2-
      c x.1 (D.op x.1 (M.op x.1 y.1)))=y.2
    rw [hd.2]
    linear_combination y.2*hi

@[implicit_reducible] def seed : Magma (Fin 4) :=
  ⟨fun x y => (![![2,3,0,1], ![3,0,1,2], ![0,1,2,3], ![1,2,3,0]] :
    Fin 4 → Fin 4 → Fin 4) x y⟩

@[implicit_reducible] def seedDivision : Magma (Fin 4) :=
  ⟨fun x y => (![![2,3,0,1], ![1,2,3,0], ![0,1,2,3], ![3,0,1,2]] :
    Fin 4 → Fin 4 → Fin 4) x y⟩

theorem seed_law : @Equation2744 (Fin 4) seed := by decide
theorem seed_division : IsDivision .left seed seedDivision := by
  change (∀ x y, seed.op x (seedDivision.op x y) = y) ∧
    (∀ x y, seedDivision.op x (seed.op x y) = y)
  decide

def offset7 : Fin 4 → Fin 4 → ZMod 7 :=
  ![![0,3,0,0], ![4,2,6,0], ![0,6,0,0], ![1,0,0,0]]

abbrev Base := Fin 4 × ZMod 7
@[implicit_reducible] def model28 : Magma Base := extension seed 4 4 offset7
@[implicit_reducible] def division28 : Magma Base := divided seedDivision 4 2 offset7

theorem model28_law : @Equation2744 Base model28 := by
  apply extension_law seed seed_law 4 4 offset7 <;> decide

theorem model28_division : IsDivision .left model28 division28 :=
  extension_division seed seedDivision seed_division 4 4 2 (by decide) offset7

/-- One bit per offset, in the same lexicographic order as the saved data.
The 28 integers encode 784 bits, rather than a 56-by-56 multiplication table. -/
def offset2 (x y : Base) : ZMod 2 :=
  let masks : Fin 4 → Fin 7 → Nat := ![
    ![236672092,201968368,210084978,46017850,227686886,72578474,55279661],
    ![160939966,171402369,55122401,81213158,49003164,238571274,19848965],
    ![22073035,153275671,174013252,261598713,232990092,72427217,65753913],
    ![35803994,40098927,40961166,120318188,112766588,5759,0]]
  if (masks x.1 ⟨x.2.val, x.2.val_lt⟩).testBit (7*y.1.val+y.2.val) then 1 else 0

@[implicit_reducible] def model56 : Magma (Base × ZMod 2) :=
  extension model28 1 1 offset2
@[implicit_reducible] def division56 : Magma (Base × ZMod 2) :=
  divided division28 1 1 offset2

theorem offset2_condition (x y : Base) :
    offset2 y y + offset2 y x + offset2 (model28.op y y) (model28.op y x) +
      offset2 (model28.op (model28.op y y) (model28.op y x)) y = 0 := by
  rcases x with ⟨i,u⟩
  rcases y with ⟨j,v⟩
  fin_cases i <;> fin_cases j <;> revert u v <;> decide +kernel

theorem model56_law : @Equation2744 (Base × ZMod 2) model56 := by
  apply extension_law model28 model28_law 1 1 offset2 (by decide) (by decide)
  simpa only [one_pow, one_mul] using offset2_condition

theorem model56_division : IsDivision .left model56 division56 :=
  extension_division model28 division28 model28_division 1 1 1 (by decide) offset2

/-- The named subterms preserve the exact seventeen-operation candidate. -/
def recovery17 {G : Type} (D : Magma G) (x : G) : G :=
  let s := D.op x x
  let a := D.op x s
  D.op (D.op (D.op a x) (D.op x (D.op s x)))
    (D.op (D.op x (D.op (D.op s (D.op (D.op x a) x)) x)) x)

/-- A single evaluation disproves the candidate. The source law and actual
division have been checked separately by the two extension arguments. -/
theorem recovery17_fails :
    recovery17 division56 ((1,0),0) ≠ model56.op ((1,0),0) ((1,0),0) := by
  decide

end Parastrophes.Eq883Extensions
