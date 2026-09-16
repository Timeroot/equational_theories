import equational_theories.Definability.Linear
import equational_theories.Definability.CloneProd
import Mathlib.Algebra.Ring.Pi

/-!
# Counting linear models obstructs term recovery

Take a finite product of distinct linear source models over a finite ring. Every
term-defined companion is coordinatewise linear. If two coordinates acquire the
same target coefficients, every recovery term also agrees on those coordinates
when its inputs agree. The original coefficients must then agree, a contradiction.
Thus there must be at least as many target coefficient pairs as source factors.

Only the small coefficient spaces are enumerated, never the product carrier or
its clone. `LinearTest` is a necessary test at six basis assignments, not an
unchecked assertion that these tests suffice for arbitrary laws.
-/

open Law Law.MagmaLaw FreeMagma

namespace Magma

variable {R : Type} [CommRing R]

/-- A cheap necessary condition for a linear operation to satisfy a law. -/
def LinearTest (L : NatMagmaLaw) (a b : R) : Prop :=
  ∀ j : Fin 6, @satisfiesPhi ℕ R (lin a b) (fun k => if k = j.val then 1 else 0) L

instance [DecidableEq R] (L : NatMagmaLaw) (a b : R) : Decidable (LinearTest L a b) := by
  unfold LinearTest satisfiesPhi
  infer_instance

theorem linearTest_of_satisfies {L : NatMagmaLaw} {a b : R}
    (h : @satisfies _ R (lin a b) L) : LinearTest L a b := fun _ => h _

/-- Equality of two coordinates is preserved whenever it holds for both inputs. -/
def RespectsCoordinates {ι : Type} (i j : ι)
    (f : (ι → R) → (ι → R) → (ι → R)) : Prop :=
  ∀ x y, x i = x j → y i = y j → f x y i = f x y j

omit [CommRing R] in
theorem respectsCoordinates_invariant {ι : Type} {i j : ι} {M : Magma (ι → R)}
    (h : RespectsCoordinates i j M.op) : M.IsCloneInvariant (RespectsCoordinates i j) where
  fst := fun _ _ hx _ => hx
  snd := fun _ _ _ hy => hy
  comp := fun _ _ hf hg x y hx hy => h _ _ (hf x y hx hy) (hg x y hx hy)

end Magma

namespace Law.MagmaLaw

open Magma

/-- More distinct source coefficients than possible target coefficients refute
even finite term-structural definability. The witness has carrier `Fin k → R`. -/
theorem not_termStructuralFromFin_of_linear_count
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {L L' : NatMagmaLaw} {k : ℕ} (a b : Fin k → R)
    (hab : Function.Injective (fun i => (a i, b i)))
    (hsource : ∀ i, @satisfies _ R (lin (a i) (b i)) L')
    (hcount : (Finset.univ.filter fun c : R × R => LinearTest L c.1 c.2).card < k) :
    ¬ L.TermStructuralFromFin L' := by
  classical
  letI : Inhabited R := ⟨0⟩
  intro h
  have hM : @satisfies _ (Fin k → R) (lin a b) L' := satisfies_piMagma hsource
  obtain ⟨N, hN, hfwd, hback⟩ := h (lin a b) hM
  obtain ⟨u, v, _, hop, _⟩ :=
    (lin_isCloneInvariant a b (a + b - 1) 1 (by ring)).of_termDefinable hfwd
  have hEq : N = lin u v := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  let T := Finset.univ.filter fun c : R × R => LinearTest L c.1 c.2
  have hT (i : Fin k) : (u i, v i) ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact linearTest_of_satisfies
      (satisfies_of_satisfies_piMagma (f := fun j => (lin (u j) (v j)).op) i hN)
  let f : Fin k → T := fun i => ⟨(u i, v i), hT i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hc : (u i, v i) = (u j, v j) := congrArg Subtype.val hij
    have hu : u i = u j := congrArg Prod.fst hc
    have hv : v i = v j := congrArg Prod.snd hc
    have hn : RespectsCoordinates i j (lin u v).op := by
      intro x y hx hy
      change u i * x i + v i * y i = u j * x j + v j * y j
      rw [hu, hv, hx, hy]
    have hm := (respectsCoordinates_invariant hn).of_termDefinable hback
    apply hab
    apply Prod.ext
    · simpa [lin_op] using hm 1 0 rfl rfl
    · simpa [lin_op] using hm 0 1 rfl rfl
  have hle := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hle
  exact not_lt_of_ge hle hcount

end Law.MagmaLaw

/-- info: 'Law.MagmaLaw.not_termStructuralFromFin_of_linear_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Law.MagmaLaw.not_termStructuralFromFin_of_linear_count
