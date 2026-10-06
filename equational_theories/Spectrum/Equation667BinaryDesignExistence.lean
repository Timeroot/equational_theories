import equational_theories.Spectrum.Equation667CommutativeDesign
import equational_theories.Spectrum.Equation667BinaryDesign

/-! Any nontrivial finite commutative idempotent E667 algebra has nonlinear
binary deformations with half of their elements idempotent. The original
algebra is retained as a quotient, and one block can carry all the asymmetry. -/
namespace Spectrum.E667.BinaryDesignExistence
open Classical
variable {Q : Type*} [Magma Q] [Finite Q]
    (h : Equation667 Q) (hc : ∀ x y : Q, x ◇ y = y ◇ x) (hi : ∀ x : Q, x ◇ x = x)

abbrev Blocks := CommutativeDesign.Block Q
def blockSet (S : Blocks (Q := Q)) : Set Q := S.val
noncomputable def coordinates (S : Blocks (Q := Q)) : blockSet S ≃ ZMod 5 :=
  (CommutativeDesign.block_coordinates h hc hi S).choose

include h hc hi in
theorem cover (x y : Q) (hxy : x ≠ y) : ∃! S : Blocks (Q := Q), x ∈ blockSet S ∧ y ∈ blockSet S :=
  CommutativeDesign.cover h hc hi x y hxy

theorem base_eq (x y : Q) : BinaryDesign.base blockSet (coordinates h hc hi) x y = x ◇ y := by
  by_cases hxy : x = y
  · subst y; rw [BinaryDesign.base_idem, hi]
  obtain ⟨S,hS,_⟩ := cover h hc hi x y hxy
  rw [BinaryDesign.base_on blockSet (coordinates h hc hi) (cover h hc hi) S ⟨x,hS.1⟩ ⟨y,hS.2⟩]
  have hm (a b : ZMod 5) :
      ((coordinates h hc hi S).symm (BinaryFive.base a b)).val =
        ((coordinates h hc hi S).symm a).val ◇ ((coordinates h hc hi S).symm b).val :=
    (CommutativeDesign.block_coordinates h hc hi S).choose_spec a b
  simpa only [Equiv.symm_apply_apply] using hm
    (coordinates h hc hi S ⟨x,hS.1⟩) (coordinates h hc hi S ⟨y,hS.2⟩)

noncomputable def singleBlock (S : Blocks (Q := Q)) : Blocks (Q := Q) → ZMod 5 → ZMod 2 :=
  fun T k => if T = S ∧ k = 0 then 1 else 0

omit [Finite Q] in
theorem singleBlock_nonconstant (S : Blocks (Q := Q)) : ¬ BinaryFive.Constant (singleBlock S S) := by
  intro hh
  have hx := hh 1
  simp only [singleBlock, eq_self, true_and, show (1 : ZMod 5) ≠ 0 by decide, if_false, if_true] at hx
  exact (by decide : (0 : ZMod 2) ≠ 1) hx

include h hc hi in
/-- A nonlinear double cover exists over every nontrivial five-design algebra. -/
theorem exists_deformation [Nontrivial Q] :
    ∃ op : (Q × ZMod 2) → (Q × ZMod 2) → (Q × ZMod 2),
      @Equation667 (Q × ZMod 2) ⟨op⟩ ∧
      (∀ x, op x x = (x.1,0)) ∧
      (∀ x y, (op x y).1 = x.1 ◇ y.1) ∧
      (¬ ∀ x y, op x y = op y x) ∧
      (¬ ∀ x y z w, op (op x y) (op z w) = op (op x z) (op y w)) ∧
      Nat.card {x : Q × ZMod 2 // op x x = x} = Nat.card Q := by
  obtain ⟨a,b,hab⟩ := exists_pair_ne Q
  obtain ⟨S,_,_⟩ := cover h hc hi a b hab
  let e := coordinates h hc hi
  let v := singleBlock S
  refine ⟨BinaryDesign.op blockSet e v, BinaryDesign.law blockSet e v (cover h hc hi),
    BinaryDesign.square blockSet e v, ?_,
    BinaryDesign.noncommutative_of_block blockSet e v (cover h hc hi) S (singleBlock_nonconstant S),
    BinaryDesign.nonmedial_of_block blockSet e v (cover h hc hi) S (singleBlock_nonconstant S),
    BinaryDesign.idempotents_card blockSet e v⟩
  intro x y
  exact base_eq h hc hi x.1 y.1

spectrum_assert base_eq complete
spectrum_assert exists_deformation complete
end Spectrum.E667.BinaryDesignExistence
