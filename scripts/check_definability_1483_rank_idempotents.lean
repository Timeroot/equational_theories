import equational_theories.Definability.FiniteSymmetry

/-! An idempotent translation image can exceed the full idempotent set in E1483. -/
namespace E1483RankIdempotentsCounterexample
def table : Array (Array (Fin 8)) := #[#[0, 3, 1, 0, 3, 1, 4, 4], #[2, 1, 5, 4, 5, 1, 4, 2], #[7, 0, 2, 0, 7, 4, 4, 2], #[4, 1, 1, 4, 1, 1, 4, 4], #[7, 3, 5, 0, 6, 1, 4, 2], #[2, 4, 2, 4, 2, 4, 4, 2], #[4, 4, 4, 4, 4, 4, 4, 4], #[0, 0, 4, 0, 0, 4, 4, 4]]
def op (x y : Fin 8) : Fin 8 := (table.getD x.val #[]).getD y.val 0
@[implicit_reducible] def model : Magma (Fin 8) := ⟨op⟩
theorem source : @Equation1483 (Fin 8) model := by decide
theorem basepoint_idempotent : op 0 0 = 0 := by decide
abbrev LeftImage := {a : Fin 8 // ∃ x : Fin 8, op 0 x = a}
abbrev Idempotents := {a : Fin 8 // op a a = a}
theorem left_card : Fintype.card LeftImage = 4 := by decide
theorem idempotent_card : Fintype.card Idempotents = 3 := by decide
theorem no_injection : ¬ ∃ f : LeftImage → Idempotents, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  rw [left_card, idempotent_card] at h
  exact (by decide : ¬ (4 ≤ 3)) h
end E1483RankIdempotentsCounterexample
/-- info: 'E1483RankIdempotentsCounterexample.source' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms E1483RankIdempotentsCounterexample.source
/-- info: 'E1483RankIdempotentsCounterexample.basepoint_idempotent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms E1483RankIdempotentsCounterexample.basepoint_idempotent
/-- info: 'E1483RankIdempotentsCounterexample.left_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E1483RankIdempotentsCounterexample.left_card
/-- info: 'E1483RankIdempotentsCounterexample.idempotent_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E1483RankIdempotentsCounterexample.idempotent_card
/-- info: 'E1483RankIdempotentsCounterexample.no_injection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E1483RankIdempotentsCounterexample.no_injection
