import equational_theories.Parastrophes.Equation883Extensions
import equational_theories.Parastrophes.Equation1516Image

/-!
# Symbolic E1516 extensions and a failed square-recovery term

The extension law below checks the fibre algebra once, over any commutative
ring. The concrete example has 133 elements, but its source-law check uses
only the 49 pairs in a seven-element base and 49 offset equations.

Its left division refutes the 24-operation candidate found on 4 November.
A second extension of order 49 refutes the subsequent 25-operation proposal.
This is a counterexample to that particular formula, not to all recovery
terms or single-equation characterizations. No catalogue attribute is attached.
-/
namespace Parastrophes.Eq1516Extensions
open Eq883Extensions (extension divided extension_division)

theorem extension_law {B R : Type} [CommRing R]
    (M : Magma B) (h : @Equation1516 B M) (a b : R) (c : B → B → R)
    (ha : a*b*(1+b)=1) (hb : a*(a+b)+b^3=0)
    (hc : ∀ x y, a*c y y + b^2*c x y + b*c x (M.op x y) +
      c (M.op y y) (M.op x (M.op x y)) = 0) :
    @Equation1516 (B × R) (extension M a b c) := by
  intro x y
  apply Prod.ext
  · exact h x.1 y.1
  · change x.2 = a*(a*y.2+b*y.2+c y.1 y.1)+
      b*(a*x.2+b*(a*x.2+b*y.2+c x.1 y.1)+c x.1 (M.op x.1 y.1))+
      c (M.op y.1 y.1) (M.op x.1 (M.op x.1 y.1))
    linear_combination -x.2*ha-y.2*hb-hc x.1 y.1

@[implicit_reducible] def seed : Magma (Fin 7) :=
  ⟨fun x y => (![
    ![1,2,3,4,5,0,6],
    ![6,3,0,2,1,5,4],
    ![5,4,2,6,0,3,1],
    ![2,5,1,0,4,6,3],
    ![4,0,5,3,6,1,2],
    ![3,1,6,5,2,4,0],
    ![0,6,4,1,3,2,5]] : Fin 7 → Fin 7 → Fin 7) x y⟩
@[implicit_reducible] def seedDivision : Magma (Fin 7) :=
  ⟨fun x y => (![
    ![5,0,1,2,3,4,6],
    ![2,4,3,1,6,5,0],
    ![4,6,2,5,1,0,3],
    ![3,2,0,6,4,1,5],
    ![1,5,6,3,0,2,4],
    ![6,1,4,0,5,3,2],
    ![0,3,5,4,2,6,1]] : Fin 7 → Fin 7 → Fin 7) x y⟩

theorem seed_law : @Equation1516 (Fin 7) seed := by decide
theorem seed_division : IsDivision .left seed seedDivision := by
  change (∀ x y, seed.op x (seedDivision.op x y) = y) ∧
    (∀ x y, seedDivision.op x (seed.op x y) = y)
  decide

def offset : Fin 7 → Fin 7 → ZMod 19 :=
  ![![6,8,0,0,13,11,0],
    ![15,4,15,15,3,15,11],
    ![0,8,0,0,0,0,6],
    ![0,8,6,0,0,10,7],
    ![7,18,0,0,0,6,0],
    ![15,14,0,1,0,0,0],
    ![0,0,0,0,0,0,0]]
abbrev Carrier := Fin 7 × ZMod 19
@[implicit_reducible] def model133 : Magma Carrier := extension seed 7 5 offset
@[implicit_reducible] def division133 : Magma Carrier := divided seedDivision 7 4 offset

theorem model133_law : @Equation1516 Carrier model133 := by
  apply extension_law seed seed_law 7 5 offset <;> decide

theorem model133_division : IsDivision .left model133 division133 :=
  extension_division seed seedDivision seed_division 7 5 4 (by decide) offset

theorem division133_inImage : InImage Law1516 .left division133 :=
  ⟨model133, (@Law1516.models_iff Carrier model133).mpr model133_law, model133_division⟩

/-- The common map in an actual image need not preserve even a square.
This blocks an endomorphism shortcut in the unrestricted converse to
Common + Short. The existing offset certificate supplies the example;
the inequality itself checks just one pair of inputs. -/
theorem turn133_not_endomorphism : ¬ ∀ x y : Carrier,
    Eq1516Image.turn division133 (division133.op x y) =
      division133.op (Eq1516Image.turn division133 x) (Eq1516Image.turn division133 y) := by
  intro h
  exact (by decide :
    Eq1516Image.turn division133 (division133.op (0,0) (0,0)) ≠
      division133.op (Eq1516Image.turn division133 (0,0))
        (Eq1516Image.turn division133 (0,0))) (h (0,0) (0,0))

/-- The exact 24-operation proposal; no minimality or completeness is claimed. -/
def recovery24 (x : Carrier) : Carrier :=
  let m := division133.op
  (m (m (m (m (m x x) (m x x)) (m (m x (m (m x x) x)) x)) (m x x)) (m (m x (m (m (m (m x x) x) (m x (m (m x x) x))) x)) (m x (m x (m x (m x x))))))

theorem recovery24_fails : recovery24 (0,0) ≠ model133.op (0,0) (0,0) := by decide


/-- A different seven-element base catches the subsequent 25-operation proposal. -/
@[implicit_reducible] def seed49 : Magma (Fin 7) :=
  ⟨fun x y => (![
    ![0,1,2,3,4,5,6],
    ![2,3,1,4,5,6,0],
    ![4,6,5,0,2,1,3],
    ![5,0,6,2,1,3,4],
    ![1,4,3,5,6,0,2],
    ![6,2,0,1,3,4,5],
    ![3,5,4,6,0,2,1]] : Fin 7 → Fin 7 → Fin 7) x y⟩
@[implicit_reducible] def seedDivision49 : Magma (Fin 7) :=
  ⟨fun x y => (![
    ![0,1,2,3,4,5,6],
    ![6,2,0,1,3,4,5],
    ![3,5,4,6,0,2,1],
    ![1,4,3,5,6,0,2],
    ![5,0,6,2,1,3,4],
    ![2,3,1,4,5,6,0],
    ![4,6,5,0,2,1,3]] : Fin 7 → Fin 7 → Fin 7) x y⟩

def offset7 : Fin 7 → Fin 7 → ZMod 7 :=
  ![![0,3,1,0,5,0,3],
    ![0,3,2,3,4,0,3],
    ![5,6,1,6,0,0,4],
    ![4,6,3,6,6,6,5],
    ![3,2,1,1,2,2,4],
    ![1,4,2,1,0,2,5],
    ![1,0,0,0,0,0,0]]
abbrev Carrier49 := Fin 7 × ZMod 7
@[implicit_reducible] def model49 : Magma Carrier49 := extension seed49 6 2 offset7
@[implicit_reducible] def division49 : Magma Carrier49 :=
  divided seedDivision49 6 4 offset7

theorem model49_law : @Equation1516 Carrier49 model49 := by
  apply extension_law seed49 (by decide) 6 2 offset7 <;> decide

theorem model49_division : IsDivision .left model49 division49 := by
  have hd : IsDivision .left seed49 seedDivision49 := by
    change (∀ x y, seed49.op x (seedDivision49.op x y) = y) ∧
      (∀ x y, seedDivision49.op x (seed49.op x y) = y)
    decide
  exact extension_division seed49 seedDivision49 hd 6 2 4 (by decide) offset7

theorem division49_inImage : InImage Law1516 .left division49 :=
  ⟨model49, (@Law1516.models_iff Carrier49 model49).mpr model49_law, model49_division⟩

def recovery25 (x : Carrier49) : Carrier49 :=
  let m := division49.op
  (m (m (m x (m x x)) (m x (m (m x (m x (m x (m (m x (m x (m x (m x x)))) x)))) x))) (m (m x (m (m x (m (m x (m x (m x (m x x)))) x)) x)) (m x (m x x))))

theorem recovery25_fails : recovery25 (1,0) ≠ model49.op (1,0) (1,0) := by decide

end Parastrophes.Eq1516Extensions
