import equational_theories.Parastrophes.Equation1516Image
import equational_theories.Parastrophes.FiniteQuasigroups
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# A column criterion for E1516's division image

The earlier converse for `Short` assumes bijective rows. There is a second
route: `Common + Short` and surjective columns suffice on finite carriers.
The key range argument itself needs no finiteness or cancellation.

Write C for the range of `turn`. The common identity says
`turn = L_y² ∘ R_y`. If R_y is onto, C is the range of L_y², hence is
preserved by L_y. Thus C is preserved by every left translation. But
`Short` writes each x as `turn(x) * (x * turn(x))`, which lies in C.
Consequently turn and every row are onto. Finiteness now supplies the
row injectivity needed by the existing converse.

This is a conditional characterization, not a single-equation result.
In fact column injectivity already extracts `Common` from `Short`, by
cancelling the common right argument. Thus the short identity is exact
among finite right quasigroups as well as among finite left quasigroups.
No quasigroup property of the candidate operation is asserted unconditionally.
-/
namespace Parastrophes.Eq1516Image

variable {G : Type} (D : Magma G)

/-- Vary the first auxiliary parameter of Short and cancel its common
right argument. This is the column counterpart of the earlier row argument. -/
theorem common_of_short_columns (hs : Short D)
    (hr : ∀ y, Function.Injective (fun x => D.op x y)) : Common D := by
  intro x y
  have he := (hs x y x).trans (hs x x x).symm
  exact hr (D.op x (cross D x x)) he

/-- The common identity identifies the range of turn with the range of
the square of any row whose corresponding column is onto. -/
theorem turn_range_closed (hc : Common D)
    (hr : ∀ y, Function.Surjective (fun x => D.op x y)) (y x : G) :
    ∃ z, turn D z = D.op y (turn D x) := by
  obtain ⟨z, hz⟩ := hr y (D.op y (D.op x y))
  change D.op z y = D.op y (D.op x y) at hz
  refine ⟨z, ?_⟩
  rw [← hc z y, ← hc x y]
  change D.op y (D.op y (D.op z y)) =
    D.op y (D.op y (D.op y (D.op x y)))
  rw [hz]

/-- Two applications of closure of the common range turn the short
identity into surjectivity. This works even on infinite carriers. -/
theorem turn_surjective_of_columns (hc : Common D) (hs : Short D)
    (hr : ∀ y, Function.Surjective (fun x => D.op x y)) :
    Function.Surjective (turn D) := by
  intro x
  obtain ⟨z, hz⟩ := turn_range_closed D hc hr x x
  obtain ⟨w, hw⟩ := turn_range_closed D hc hr (turn D x) z
  refine ⟨w, ?_⟩
  rw [hw, hz]
  exact hs x x x

/-- Surjective columns force surjective rows under the two proposed
identities; no finite-cardinality argument is used in this direction. -/
theorem rows_surjective_of_columns (hc : Common D) (hs : Short D)
    (hr : ∀ y, Function.Surjective (fun x => D.op x y)) :
    ∀ y, Function.Surjective (D.op y) := by
  intro y x
  obtain ⟨z, rfl⟩ := turn_surjective_of_columns D hc hs hr x
  exact ⟨D.op y (D.op z y), hc z y⟩

/-- A second exact finite criterion. The column assumption is essential:
`Equation1516CommonCounterexample` disproves its consequence from the two
identities alone. -/
theorem characterizes_columns_fin [Finite G] :
    (Common D ∧ Short D ∧
      ∀ y, Function.Surjective (fun x => D.op x y)) ↔
      InImage Law1516 .left D := by
  constructor
  · rintro ⟨hc, hs, hr⟩
    have hl := rows_surjective_of_columns D hc hs hr
    have hq : IsSideQuasigroup .left D := fun y =>
      ⟨Finite.injective_iff_surjective.mpr (hl y), hl y⟩
    exact (characterizes_leftQuasigroups_fin D hq).mp hs
  · intro h
    obtain ⟨M, hM, hd⟩ := h
    have hm := (@Law1516.models_iff G M).mp hM
    have hq := division_quasigroup
      (Catalogue.quasigroup1516_fin G M (show Finite G from inferInstance) hM) hd
    exact ⟨(forward M D hd hm).1,
      short_of_image D ⟨M, hM, hd⟩, fun y => (hq.2 y).2⟩

/-- Either side of the quasigroup hypothesis suffices for the short
identity's converse on finite carriers. -/
theorem characterizes_rightQuasigroups_fin [Finite G]
    (hr : IsSideQuasigroup .right D) : Short D ↔ InImage Law1516 .left D := by
  constructor
  · intro hs
    exact (characterizes_columns_fin D).mp
      ⟨common_of_short_columns D hs (fun y => (hr y).1), hs,
        fun y => (hr y).2⟩
  · exact short_of_image D

/-- Finite countermodel searches for the short identity may always select
an actual collision in a column. This concerns a proposed identity, not
an obstruction to every single-equation characterization. -/
theorem column_collision_of_not_image_fin [Finite G] (hs : Short D)
    (hn : ¬ InImage Law1516 .left D) :
    ∃ y x z, x ≠ z ∧ D.op x y = D.op z y := by
  classical
  by_contra! h
  have hi (y : G) : Function.Injective (fun x => D.op x y) := by
    intro x z he
    by_contra hx
    exact h y x z hx he
  have hr : IsSideQuasigroup .right D := fun y =>
    ⟨hi y, Finite.surjective_of_injective (hi y)⟩
  exact hn ((characterizes_rightQuasigroups_fin D hr).mp hs)

/-! Inserting repeated instances of the fixed-point identity is a natural
way to try to strengthen Short. The existing four-element counterexample
rules out this whole family, for arbitrary exponents, not just a bounded
search through candidate terms. -/

def shiftedCross (k : ℕ) (x y : G) : G :=
  (fun t => D.op t x)^[k] (cross D x y)

def ShiftedShort (k l : ℕ) : Prop :=
  ∀ x y z, D.op (shiftedCross D k x y) (D.op x (shiftedCross D l x z)) = x

theorem shiftedCross_of_criterion (hc : Common D) (hf : Fixed D)
    (k : ℕ) (x y : G) : shiftedCross D k x y = turn D x := by
  unfold shiftedCross
  rw [hc]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    exact hf x

theorem shiftedShort_of_image_fin [Finite G] (h : InImage Law1516 .left D)
    (k l : ℕ) : ShiftedShort D k l := by
  obtain ⟨M, hM, hd⟩ := h
  obtain ⟨hc, hf⟩ := forward M D hd ((@Law1516.models_iff G M).mp hM)
  have hs := short_of_image D ⟨M, hM, hd⟩
  intro x y z
  rw [shiftedCross_of_criterion D hc hf, shiftedCross_of_criterion D hc hf]
  exact hs x x x

/-- On the cross values of the saved four-element counterexample, each
right translation has period dividing two. -/
theorem shortCounterexample_cross_period (x y : Fin 4) :
    Function.IsPeriodicPt (fun t => shortCounterexample.op t x) 2
      (cross shortCounterexample x y) := by
  revert x y
  decide

/-- Four small checks, followed by reduction of arbitrary exponents modulo
two, refute every proposed strengthening in this family. -/
theorem shortCounterexample_shiftedShort (k l : ℕ) :
    ShiftedShort shortCounterexample k l := by
  have small : ∀ k l : Fin 2, ShiftedShort shortCounterexample k.val l.val := by
    unfold ShiftedShort shiftedCross
    decide
  intro x y z
  unfold shiftedCross
  rw [← (shortCounterexample_cross_period x y).iterate_mod_apply k,
    ← (shortCounterexample_cross_period x z).iterate_mod_apply l]
  exact small ⟨k % 2, Nat.mod_lt _ (by decide)⟩
    ⟨l % 2, Nat.mod_lt _ (by decide)⟩ x y z

/-- No member of this infinite candidate family characterizes the finite
image. This does not rule out other single identities. -/
theorem shiftedShort_not_characterization_fin (k l : ℕ) :
    ¬ (∀ (A : Type) [Finite A] (M : Magma A),
      ShiftedShort M k l ↔ InImage Law1516 .left M) := by
  intro h
  exact shortCounterexample_not_image
    ((h (Fin 4) shortCounterexample).mp (shortCounterexample_shiftedShort k l))

end Parastrophes.Eq1516Image
