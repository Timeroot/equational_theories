import equational_theories.Spectrum.Equation1083_1286.CommonPointWitnesses
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation

/-! A pointed E1286 model on five binary coordinates. The data are two
5-by-5 matrices; only their coefficient identities are checked, not all
pairs of the 32-element carrier. Common-point gluing gives order 218. -/
namespace Spectrum.E1083E1286.BinarySeed
open Law Law.MagmaLaw Matrix

def left : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![![0,0,1,0,1], ![0,0,0,1,0], ![0,0,0,0,1], ![1,0,1,0,1], ![0,1,0,1,0]]

def right : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![![0,1,1,0,0], ![1,0,1,1,0], ![1,1,0,1,1], ![1,0,0,0,1], ![1,1,0,0,0]]

theorem left_coefficient : right*left*(left*left+right) = 1 := by
  have h : ∀ i j : Fin 5, (right*left*(left*left+right)) i j = (1 : Matrix _ _ _) i j := by
    decide
  exact funext fun i => funext (h i)

theorem right_coefficient : left+right*(left*left*right+right) = 0 := by
  have h : ∀ i j : Fin 5, (left+right*(left*left*right+right)) i j = 0 := by decide
  exact funext fun i => funext (h i)

def operation (x y : Fin 5 → ZMod 2) := left *ᵥ x + right *ᵥ y

theorem lawful : Lawful true operation := by
  intro x y
  change left *ᵥ y + right *ᵥ
    (left *ᵥ (left *ᵥ (left *ᵥ x + right *ᵥ y) + right *ᵥ x) + right *ᵥ y) = x
  calc
    _ = (right*left*(left*left+right)) *ᵥ x +
        (left+right*(left*left*right+right)) *ᵥ y := by
      simp only [Matrix.mulVec_add, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
      abel
    _ = x := by rw [left_coefficient, right_coefficient]; simp

def pointed32 : Pointed true (Fin 5 → ZMod 2) where
  op := operation
  lawful := lawful
  point := 0
  fixed := by simp [operation]

theorem model32 : Law1286.HasModel 32 := pointed32.hasModel (by simp)

theorem model218 : Law1286.HasModel 218 :=
  common_point_model
    (PBD.HasTD.primePower (k := 7) (p := 31) (e := 1) (by norm_num) (by decide) (by decide))
    idem7 pointed32 (by simp)

/-- A second quartic family, starting with the 218-element model. -/
theorem quartic_family (t : ℕ) : Law1286.HasModel (224*(30*t+1)^4-6) := by
  let m := 30*t+1
  let q := 32*m^4-1
  letI : NeZero m := ⟨by dsimp [m]; omega⟩
  have hm : m % 30 = 1 := by dsimp [m]; omega
  have hp : 0 < m^4 := pow_pos (by dsimp [m]; omega) _
  have hq : 0 < q := by dsimp [q]; omega
  have hc : q+1 = 32*m^4 := by dsimp [q]; omega
  have hmod : (q+1)%30 = 2 := by
    rw [hc]
    norm_num [Nat.mul_mod, Nat.pow_mod, hm]
  have hcop : q.Coprime 30 := by
    have hr : q%30 = 1 := by omega
    change Nat.gcd q 30 = 1
    rw [Nat.gcd_comm q 30, Nat.gcd_rec 30 q, hr]
    decide
  have h := common_point_model (cyclic7 hq hcop) idem7
    (pointed32.product (quarticPointed m true)) (show _ = q+1 from by
      simpa [pow_succ, Nat.mul_assoc] using hc.symm)
  convert h using 1
  change 224*m^4-6 = 7*q+1
  omega

spectrum_assert model32 complete
spectrum_assert model218 complete
spectrum_assert quartic_family complete

/-- info: 'Spectrum.E1083E1286.BinarySeed.model218' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model218

end Spectrum.E1083E1286.BinarySeed
