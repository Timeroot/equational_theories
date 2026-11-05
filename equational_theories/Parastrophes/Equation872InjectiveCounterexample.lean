import equational_theories.Parastrophes.Equation872InjectiveCandidate
import Mathlib.Data.Fin.VecNotation

/-!
# A six-element refutation of the 28-operation E872 image candidate

The candidate supplies its own row cancellation, and the converse had been
proved for idempotent magmas. Nevertheless neither fact establishes its
general converse. The table below satisfies the full three-variable candidate
and has bijective rows, but `0 * c(0) = 4`, contradicting the unit identity
required of every actual E872 left-division image.

Rows 0, 3, and 4 coincide. This is precisely the distinction retained by the
earlier row-permutation lemmas: equal rows need not have equal indices.
The SAT solver discovered the table; Lean checks the table itself. No SAT
certificate, trusted solver result, or native decision is needed.
-/
namespace Parastrophes.Eq872InjectiveCounterexample
open Law Eq872Image Eq872InjectiveCandidate

@[implicit_reducible] def bad : Magma (Fin 6) :=
  ⟨fun x y => (![![1, 0, 3, 2, 5, 4],
    ![4, 2, 1, 5, 3, 0],
    ![0, 1, 2, 3, 5, 4],
    ![1, 0, 3, 2, 5, 4],
    ![1, 0, 3, 2, 5, 4],
    ![3, 1, 2, 0, 4, 5]] : Fin 6 → Fin 6 → Fin 6) x y⟩

theorem candidate : Candidate bad := by
  unfold Candidate Frame adjustedCore bridge unit core
  decide

/-- Cancellation on the required side is already a consequence of the
candidate. The counterexample is not exploiting a missing row inverse. -/
theorem bijective_rows : IsSideQuasigroup .left bad := rows_fin bad candidate

theorem failed_unit : bad.op 0 (core bad 0) = 4 := by decide

theorem not_image : ¬ InImage Law872 .left bad := by
  intro h
  have hu := ((Eq872Image.characterizes_fin bad).mpr h).1 0
  change (0 : Fin 6) = bad.op 0 (core bad 0) at hu
  rw [failed_unit] at hu
  exact (by decide : (0 : Fin 6) ≠ 4) hu

/-- The candidate fails as a characterization even on finite carriers. -/
theorem no_converse :
    ¬ (∀ (G : Type) [Finite G] (D : Magma G),
      Candidate D → InImage Law872 .left D) := by
  intro h
  exact not_image (h (Fin 6) bad candidate)

end Parastrophes.Eq872InjectiveCounterexample
