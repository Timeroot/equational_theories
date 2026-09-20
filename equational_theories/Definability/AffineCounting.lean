import equational_theories.Definability.LinearCounting
import equational_theories.Definability.AffineClone

/-!
# Counting affine models obstructs mutual term recovery

Take a product of distinct affine source operations over a finite commutative
ring. Every term-defined companion remains coordinatewise affine. Recovery
forces distinct source coordinates to have distinct target coefficient triples.
The constant coefficient is read at (0,0), then the linear coefficients at
(1,0) and (0,1). Thus too few target triples refute term recovery, even finitely.

`AffineTest` supplies necessary conditions only. Source identities must be
proved separately; the target test makes no sufficiency assumption.
-/

open Law Law.MagmaLaw FreeMagma Magma

namespace Magma
variable {R : Type} [CommRing R]
/-- Necessary zero and unit-assignment tests for an affine operation. -/
def AffineTest (L : NatMagmaLaw) (a b c : R) : Prop :=
  @satisfiesPhi ℕ R (aff a b c) (fun _ => 0) L ∧
  ∀ j : Fin 6, @satisfiesPhi ℕ R (aff a b c) (fun k => if k = j.val then 1 else 0) L
instance [DecidableEq R] (L : NatMagmaLaw) (a b c : R) : Decidable (AffineTest L a b c) := by
  unfold AffineTest satisfiesPhi
  infer_instance
theorem affineTest_of_satisfies {L : NatMagmaLaw} {a b c : R}
    (h : @satisfies _ R (aff a b c) L) : AffineTest L a b c := ⟨h _, fun _ => h _⟩
end Magma

namespace Law.MagmaLaw
theorem not_termStructuralFromFin_of_affine_count
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {L L' : NatMagmaLaw} {k : ℕ} (a b c : Fin k → R)
    (hab : Function.Injective (fun i => (a i, b i, c i)))
    (hsource : ∀ i, @satisfies _ R (aff (a i) (b i) (c i)) L')
    (hcount : (Finset.univ.filter fun c : R × R × R => AffineTest L c.1 c.2.1 c.2.2).card < k) :
    ¬ L.TermStructuralFromFin L' := by
  classical
  letI : Inhabited R := ⟨0⟩
  intro h
  have hM : @satisfies _ (Fin k → R) (aff a b c) L' := satisfies_piMagma hsource
  obtain ⟨N, hN, hfwd, hback⟩ := h (aff a b c) hM
  obtain ⟨q, r, hop⟩ := (aff_isCloneInvariant a b c).of_termDefinable hfwd
  let u := 1 - q + r * (a + b - 1)
  let v := q
  let w := r * c
  have hEq : N = aff u v w := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  let T := Finset.univ.filter fun c : R × R × R => AffineTest L c.1 c.2.1 c.2.2
  have hT (i : Fin k) : (u i, v i, w i) ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact affineTest_of_satisfies
      (satisfies_of_satisfies_piMagma (f := fun j => (aff (u j) (v j) (w j)).op) i hN)
  let f : Fin k → T := fun i => ⟨(u i, v i, w i), hT i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hc : (u i, v i, w i) = (u j, v j, w j) := congrArg Subtype.val hij
    have hu : u i = u j := congrArg Prod.fst hc
    have hv : v i = v j := congrArg (fun p => p.2.1) hc
    have hw : w i = w j := congrArg (fun p => p.2.2) hc
    have hn : RespectsCoordinates i j (aff u v w).op := by
      intro x y hx hy
      change u i * x i + v i * y i + w i = u j * x j + v j * y j + w j
      rw [hu, hv, hw, hx, hy]
    have hm := (respectsCoordinates_invariant hn).of_termDefinable hback
    have hc0 : c i = c j := by simpa [aff_op] using hm 0 0 rfl rfl
    have ha : a i = a j := by
      have h := hm 1 0 rfl rfl
      simpa [aff_op, hc0] using h
    have hb : b i = b j := by
      have h := hm 0 1 rfl rfl
      simpa [aff_op, hc0] using h
    apply hab
    exact Prod.ext ha (Prod.ext hb hc0)
  have hle := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hle
  exact not_lt_of_ge hle hcount

end Law.MagmaLaw
/-- info: 'Law.MagmaLaw.not_termStructuralFromFin_of_affine_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.not_termStructuralFromFin_of_affine_count
