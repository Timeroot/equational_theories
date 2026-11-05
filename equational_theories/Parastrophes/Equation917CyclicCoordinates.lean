import equational_theories.Parastrophes.Equation917CompositionCandidate
import Mathlib.Tactic.Abel

/-!
# Cyclic coordinates for the remaining E917 permutation obstruction

The open composition candidate supplies a quasigroup and permutations satisfying
`x*b(y)=a(x*y)`. If a is one cycle, so is b. Label that cycle additively.
Every multiplication table then has the form `u(x)+v(y)`, where u and v are
permutations and v(0)=0. This reduces a search over an entire Latin square to
two permutations. Neither permutation is asserted to be a group homomorphism.

The calculation below applies to any quasigroup with this conjugacy, not just
E917, and uses no finiteness beyond the orbit/coordinate hypotheses. It is a
search reduction, not a characterization of the division image.
-/
namespace Parastrophes.Eq917Image.CompositionCandidate

variable {A : Type} (D : Magma A)

/-- A transitive output permutation gives a transitive input permutation by
conjugating along one row. -/
theorem input_orbit_of_output_orbit (a b : A → A) (hq : IsQuasigroup D)
    (shift : ∀ x y, D.op x (b y) = a (D.op x y)) (o : A)
    (orbit : ∀ y, ∃ n : ℕ, (a^[n]) (D.op o o) = y) :
    ∀ y, ∃ n : ℕ, (b^[n]) o = y := by
  have hi (n : ℕ) : D.op o ((b^[n]) o) = (a^[n]) (D.op o o) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', shift, ih]
  intro y
  obtain ⟨n, hn⟩ := orbit (D.op o y)
  exact ⟨n, (hq.1 o).1 ((hi n).trans hn)⟩

/-- An additive labeling turns the multiplication into the sum of two
bijective coordinate maps. In the single-cycle finite case use C = ZMod n
and step = 1. -/
theorem cyclic_coordinates {C : Type} [AddCommGroup C]
    (a b : A → A) (hq : IsQuasigroup D)
    (shift : ∀ x y, D.op x (b y) = a (D.op x y))
    (e : A ≃ C) (step : C) (label : ∀ x, e (a x) = e x + step)
    (o : A) (orbit : ∀ y, ∃ n : ℕ, (b^[n]) o = y) :
    ∃ u v : A → C, Function.Bijective u ∧ Function.Bijective v ∧
      v o = 0 ∧ ∀ x y, e (D.op x y) = u x + v y := by
  let u := fun x => e (D.op x o)
  let v := fun y => e (D.op o y) - e (D.op o o)
  have ub : Function.Bijective u := e.bijective.comp (hq.2 o)
  have vb : Function.Bijective v := by
    constructor
    · intro x y he
      apply (hq.1 o).1
      apply e.injective
      have hh := congrArg (fun t => t + e (D.op o o)) he
      simpa only [v, sub_add_cancel] using hh
    · intro y
      obtain ⟨z, hz⟩ := (e.bijective.comp (hq.1 o)).2 (y + e (D.op o o))
      refine ⟨z, ?_⟩
      change e (D.op o z) - e (D.op o o) = y
      change e (D.op o z) = y + e (D.op o o) at hz
      rw [hz, add_sub_cancel_right]
  have along (x : A) (n : ℕ) :
      e (D.op x ((b^[n]) o)) = e (D.op x o) + n • step := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, zero_nsmul, add_zero]
    | succ n ih =>
      rw [Function.iterate_succ_apply', shift, label, ih, succ_nsmul]
      abel
  refine ⟨u, v, ub, vb, sub_self _, ?_⟩
  intro x y
  obtain ⟨n, rfl⟩ := orbit y
  dsimp only [u, v]
  rw [along, along]
  abel

end Parastrophes.Eq917Image.CompositionCandidate
