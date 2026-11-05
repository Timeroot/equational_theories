import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.Basic

namespace Parastrophes

/-- In a finite family, permuting which member supplies a right inverse at
 each point already forces every member to be bijective. The carrier itself
 need not be finite. -/
theorem finite_inverse_family {I G : Type*} [Finite I]
    (f : I → G → G) (p : G → Equiv.Perm I)
    (h : ∀ i x, f i (f (p x i) x) = x) :
    ∀ i, Function.Bijective (f i) := by
  have back (i : I) (x : G) : f ((p x).symm i) (f i x) = x := by
    simpa using h ((p x).symm i) x
  have unique (i : I) (x y : G) (hy : f i y = x) : y = f (p x i) x := by
    let z (j : I) := f (p x j) x
    let tag (j : I) := (p (z j)).symm j
    have recover (j : I) : f (tag j) x = z j := by
      have hh := back j (z j)
      simpa only [z, h] using hh
    have hi : Function.Injective tag := by
      intro j k he
      have hz : z j = z k := by
        simpa only [recover] using congrArg (fun t => f t x) he
      dsimp [tag] at he
      rw [hz] at he
      exact (p (z k)).symm.injective he
    obtain ⟨j, hj⟩ := Finite.surjective_of_injective hi ((p y).symm i)
    have hz : z j = y := by
      rw [← recover, hj, ← hy]
      exact back i y
    have hji : j = i := by
      dsimp [tag] at hj
      rw [hz] at hj
      exact (p y).symm.injective hj
    subst j
    exact hz.symm
  intro i
  refine ⟨?_, fun x => ⟨f (p x i) x, h i x⟩⟩
  intro x y he
  exact (unique i (f i x) x rfl).trans (unique i (f i x) y he.symm).symm

end Parastrophes
