import equational_theories.Definability.Central1483Translations

/-! The ten-leaf candidate specializes to the opposite operation on every
central groupoid. Its behavior under E1483 alone remains unproved. -/

namespace CentralCandidate

def candidate {G : Type*} [Magma G] (x y : G) : G :=
  ((x ◇ y) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (x ◇ ((y ◇ y) ◇ x)))

/-- The candidate's diagonal is the third iterate of the source diagonal.
This does not establish the conjectural identity `q³ = q`. -/
theorem diagonal {G : Type*} [Magma G] (h : Equation1483 G) (x : G) :
    candidate x x = ((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)) := by
  unfold candidate
  rw [CentralDual.left_regular h x x]

theorem central_opposite {G : Type*} [Magma G] (h : Equation168 G) (x y : G) :
    candidate x y = y ◇ x := by
  unfold candidate
  rw [← h x x ((y ◇ y) ◇ x), ← h y x y]

@[implicit_reducible] def target {G : Type*} (source : Magma G) : Magma G where
  op := @candidate G source

theorem central_target {G : Type*} [Magma G] (h : Equation168 G) :
    @Equation1479 G (target inferInstance) := by
  change ∀ x y, x = candidate (candidate y x) (candidate x (candidate x y))
  intro x y
  simp only [central_opposite h]
  exact h x (y ◇ x) y

/-- info: 'CentralCandidate.central_opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms central_opposite

/-- info: 'CentralCandidate.diagonal' does not depend on any axioms -/
#guard_msgs in
#print axioms diagonal

/-- info: 'CentralCandidate.central_target' does not depend on any axioms -/
#guard_msgs in
#print axioms central_target

end CentralCandidate
