import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Structural facts about the images of multiplication by squares in E1486. -/
namespace Spectrum.E1486.SquareRows

abbrev Lawful {G : Type*} (f : G → G → G) :=
  ∀ x y z, f (f y x) (f x (f z z)) = x

variable {G : Type*} (f : G → G → G) (h : Lawful f)

include h in
theorem square_tripotent (x : G) : f (f (f x x) (f x x)) (f (f x x) (f x x)) = f x x :=
  h (f x x) (f x x) x

include h in
theorem absorption (x y z : G) :
    f x (f (f x (f y y)) (f z z)) = f x (f y y) := by
  have h1 := h x x y
  have h2 := h (f x (f y y)) (f x x) z
  rw [h1] at h2
  exact h2

section Finite
variable [Fintype G] [DecidableEq G]

def row (x : G) : Finset G := Finset.univ.image (fun z => f x (f z z))

@[simp] theorem mem_row (x u : G) : u ∈ row f x ↔ ∃ z, f x (f z z) = u := by
  simp [row]

theorem row_nonempty [Nonempty G] (x : G) : (row f x).Nonempty := by
  obtain ⟨z⟩ := ‹Nonempty G›
  exact ⟨_, (mem_row f x _).mpr ⟨z,rfl⟩⟩

include h in
theorem return_on_row (x y : G) (hy : y ∈ row f x) (u : G) (hu : u ∈ row f y) :
    f x u = y := by
  obtain ⟨a, rfl⟩ := (mem_row f x y).mp hy
  obtain ⟨b, rfl⟩ := (mem_row f (f x (f a a)) u).mp hu
  exact absorption f h x a b

include h in
theorem row_disjoint (x : G) : (↑(row f x) : Set G).PairwiseDisjoint (row f) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro u hua hub
  exact hab ((return_on_row f h x a ha u hua).symm.trans (return_on_row f h x b hb u hub))

include h in
theorem square_two_step (x z : G) : f z z ∈ (row f x).biUnion (row f) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨f x (f z z), (mem_row f x _).mpr ⟨z,rfl⟩, ?_⟩
  apply (mem_row f _ _).mpr
  exact ⟨f z z, h (f z z) x z⟩

include h in
/-- A minimum square-row rank r satisfies r² ≤ the order of the magma. -/
theorem exists_small_row [Nonempty G] :
    ∃ a : G, 0 < (row f a).card ∧ (row f a).card ^ 2 ≤ Fintype.card G := by
  obtain ⟨a, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun x => (row f x).card) Finset.univ_nonempty
  refine ⟨a, Finset.card_pos.mpr (row_nonempty f a), ?_⟩
  have hsum : (row f a).card * (row f a).card ≤ ∑ x ∈ row f a, (row f x).card := by
    simpa using (Finset.sum_le_sum (s := row f a)
      (f := fun _ => (row f a).card) (g := fun x => (row f x).card)
      (fun x _ => hmin x (Finset.mem_univ x)))
  have hcard : ((row f a).biUnion (row f)).card ≤ Fintype.card G :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  rw [Finset.card_biUnion (row_disjoint f h a)] at hcard
  simpa [pow_two] using hsum.trans hcard

end Finite

/-- info: 'Spectrum.E1486.SquareRows.exists_small_row' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_small_row

end Spectrum.E1486.SquareRows
