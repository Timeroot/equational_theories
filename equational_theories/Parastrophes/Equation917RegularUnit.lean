import equational_theories.Parastrophes.Equation917CrossCalculations
import equational_theories.Parastrophes.Equation917DoubleUnitCandidate
import equational_theories.Parastrophes.Equation917PowerComparison

/-!
# A regular unit map in an E917 crossed magma

Put q(x)=(x*(x*x))*x and U(x)=x*q(x). Assume the crossed identity
`y*(q(x)*(x*y))=x`, and suppose a common map w satisfies
`x*U(y)=w(x*y)`. On finite carriers, w and U are inverse permutations.
Moreover `U(x)*y=U(x*y)`, `U(x)*U(y)=x*y`, and `q(U(x))=q(x)`.

This is a reduction of a remaining converse problem, NOT a characterization.
In particular, the theorem does not assert U=id. The orbit relation of U
respects multiplication. `Equation917UnitQuotient.lean` constructs the finite
quotient and proves it is a genuine division image. Excluding all nontrivial
extensions remains open.
-/
namespace Parastrophes.Eq917Image.RegularUnit
open SandwichCandidate (U H)

theorem inverse_unit {A : Type} [Finite A] (D : Magma A) (h : Cross D)
    (w : A → A) (hw : ∀ x y, D.op x (U D y) = w (D.op x y)) (x : A) :
    w (U D x) = x := by
  have hh := h x x
  have he : U D (core D x) = D.op (core D x) (D.op x x) := by
    unfold U
    rw [CrossCalculations.core_core D h]
  rw [← he, hw] at hh
  exact hh.symm

/-- The regularity assumption gives inverse permutations and a pair of
compatible left/right actions. No claim that either permutation is trivial. -/
theorem reduction {A : Type} [Finite A] (D : Magma A) (h : Cross D)
    (w : A → A) (hw : ∀ x y, D.op x (U D y) = w (D.op x y)) :
    Function.Bijective (U D) ∧ Function.Bijective w ∧
      (∀ x, w (U D x) = x) ∧ (∀ x, U D (w x) = x) ∧
      (∀ x y, D.op (U D x) y = U D (D.op x y)) ∧
      (∀ x y, D.op (U D x) (U D y) = D.op x y) ∧
      (∀ x, core D (U D x) = core D x) := by
  have wu := inverse_unit D h w hw
  have ui : Function.Injective (U D) := Function.LeftInverse.injective wu
  have us : Function.Surjective (U D) := Finite.surjective_of_injective ui
  have uw (x) : U D (w x) = x := by
    obtain ⟨y, rfl⟩ := us x
    rw [wu]
  have wb : Function.Bijective w :=
    ⟨Function.LeftInverse.injective uw, fun x => ⟨U D x, wu x⟩⟩
  have hq := Candidate.quasigroup_of_frame D (fun x _ => core D x)
    (fun x y _ => h x y)
  have row_w (x y) : D.op x (w y) = U D (D.op x y) := by
    have hh := congrArg (U D) (hw x (w y))
    simpa only [uw] using hh.symm
  have hu (x y) : H D x (U D y) = U D (H D x y) := by
    unfold H
    rw [hw, row_w]
  have inv (x y) : D.op (U D x) (U D y) = D.op x y := by
    let t := D.op x y
    have he : H D t x = y := (hq.1 x).1 (h t x).symm
    have hh := h t (U D x)
    change t = D.op (U D x) (H D t (U D x)) at hh
    rw [hu, he] at hh
    exact hh.symm
  have left (x y) : D.op (U D x) y = U D (D.op x y) := by
    calc
      _ = D.op (U D x) (U D (w y)) := by rw [uw]
      _ = D.op x (w y) := inv x (w y)
      _ = _ := row_w x y
  refine ⟨⟨ui, us⟩, wb, wu, uw, left, inv, ?_⟩
  intro x
  unfold core
  rw [inv, left, inv]

/-- A fixed point would finish this special converse problem. The missing
step is establishing such a point without an additional hypothesis. -/
theorem unit_eq_of_fixed_point {A : Type} [Finite A] (D : Magma A) (h : Cross D)
    (w : A → A) (hw : ∀ x y, D.op x (U D y) = w (D.op x y))
    (a : A) (ha : U D a = a) : ∀ x, U D x = x := by
  have hr := (reduction D h w hw).2.2.2.2.1
  have rows := (Candidate.quasigroup_of_frame D (fun x _ => core D x)
    (fun x y _ => h x y)).1
  intro x
  obtain ⟨y, rfl⟩ := (rows a).2 x
  exact (hr a y).symm.trans (by rw [ha])

/-- The twenty-operation candidate still admits every regular-unit crossed
magma. Thus its converse includes the unresolved regular-unit problem. -/
theorem double_unit_candidate {A : Type} [Finite A] (D : Magma A) (h : Cross D)
    (w : A → A) (hw : ∀ x y, D.op x (U D y) = w (D.op x y)) :
    DoubleUnitCandidate.Identity D := by
  obtain ⟨_, _, _, uw, left, _, _⟩ := reduction D h w hw
  have cmp (t z y : A) :
      D.op (U D t) (D.op (U D z) y) = D.op t (D.op z y) := by
    rw [left z y, left t (U D (D.op z y)), hw, uw]
  intro x y z t v
  rw [cmp]
  exact h x _

/-- Applying U twice in the first compared slot and once in the second
eliminates this obstruction: within the regular-unit class, the modified
comparison forces U=id. This is deliberately a conditional result. -/
theorem basis_of_power_comparison {A : Type} [Finite A] (D : Magma A) (h : Cross D)
    (w : A → A) (hw : ∀ x y, D.op x (U D y) = w (D.op x y))
    (hc : PowerComparison.Identity D) : Basis D := by
  obtain ⟨_, _, _, uw, left, _, _⟩ := reduction D h w hw
  have cmp (t z y : A) :
      D.op (U D t) (D.op (U D z) y) = D.op t (D.op z y) := by
    rw [left z y, left t (U D (D.op z y)), hw, uw]
  have cmp2 (t z y : A) :
      D.op (U D (U D t)) (D.op (U D z) y) = U D (D.op t (D.op z y)) := by
    rw [left (U D t) (D.op (U D z) y), cmp]
  refine ⟨?_, h⟩
  intro x
  have he := hc x x x x x
  rw [cmp2, left, left, H, ← h x _] at he
  exact he

end Parastrophes.Eq917Image.RegularUnit
