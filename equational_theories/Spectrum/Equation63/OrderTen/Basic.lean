import equational_theories.Spectrum.Basic
import equational_theories.Equations.Eqns1_999

/-!
# The mathematical reductions for the order-ten exclusion

Left division turns finite E63 into `((x * (x * y)) * x) = y` (E229).
Its translations are permutations, with `Rₓ = Lₓ⁻²`. In particular the
cycle of `x` under `Lₓ` has length one or three, and no `Lₓ` has a two-cycle.
-/
namespace Spectrum.E63.OrderTen

abbrev Cubic {A : Type*} (f : A → A → A) : Prop :=
  ∀ x y, f (f x (f x y)) x = y

variable {A : Type*} [Finite A] {f : A → A → A}

theorem right_injective (h : Cubic f) (x : A) :
    Function.Injective (fun y => f y x) := by
  apply Finite.injective_iff_surjective.mpr
  exact fun y => ⟨f x (f x y), h x y⟩

omit [Finite A] in
theorem left_injective (h : Cubic f) (x : A) : Function.Injective (f x) := by
  intro y z he
  have := congrArg (fun a => f (f x a) x) he
  simpa only [h] using this

theorem own_cube (h : Cubic f) (x : A) : f x (f x (f x x)) = x := by
  apply right_injective h x
  exact h x (f x x)

theorem no_two_cycle (h : Cubic f) (x y z : A) (hy : f x y = z)
    (hz : f x z = y) : y = z := by
  have hr : f y x = y := by simpa only [hy, hz] using h x y
  -- The three-cycle through y contains x, since y*x=y.
  have hyy : f y (f y y) = x := by
    apply left_injective h y
    simpa only [hr] using own_cube h y
  have hxy : f x y = y := by
    simpa only [hyy] using h y y
  exact hxy.symm.trans hy

omit [Finite A] in
/-- Relabelling preserves the cubic law. -/
theorem cubic_relabel (h : Cubic f) (e : A ≃ A) :
    Cubic (fun x y => e (f (e.symm x) (e.symm y))) := by
  intro x y
  simp only [Equiv.symm_apply_apply, h, Equiv.apply_symm_apply]

/-- Left division of a finite E63 magma satisfies E229. This construction
uses only the inverse permutations of the original left translations. -/
theorem cubic_of_e63 [Magma A] (h : Equation63 A) : ∃ f : A → A → A, Cubic f := by
  classical
  have hl (x : A) : Function.Bijective (fun y : A => x ◇ y) := by
    have hs : Function.Surjective (fun y : A => x ◇ y) :=
      fun y => ⟨y ◇ (y ◇ x), (h y x).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  let L (x : A) := Equiv.ofBijective (fun y : A => x ◇ y) (hl x)
  let d (x y : A) := (L x).symm y
  have hd (x y : A) : x ◇ d x y = y := (L x).apply_symm_apply y
  have formula (x y : A) : d x y = y ◇ (y ◇ x) := by
    apply (hl x).1
    change x ◇ d x y = x ◇ (y ◇ (y ◇ x))
    rw [hd, ← h]
  refine ⟨d, fun x y => ?_⟩
  rw [formula (d x (d x y)) x, hd, hd]

end Spectrum.E63.OrderTen
