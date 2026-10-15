import equational_theories.Definability.FiniteBridge
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Pigeonhole

/-!
# E3272 from a retraction with a second section

A retraction `e` together with a second point `s x` in the fiber of `e x`
provides an E3272 operation by a three-way case distinction. No source identity
is required. On a finite magma this is FO-definable whenever the two maps are
automorphism-invariant.

In particular, this applies when every nonempty square fiber has exactly two
elements: the other element of the fiber is canonically defined. An eventual
idempotent power of squaring supplies the retraction. This is a conditional
magma-level construction, not an unconditional law-to-law arrow.
-/

open Law Law.MagmaLaw
namespace SplitRetraction3272
variable {G : Type}

/-- A second section makes it possible to return through a different fiber
without retaining the first input's extra coordinates. -/
noncomputable def operation (e s : G → G) (x y : G) : G := by
  classical
  exact if e x = e y then e x else if y = e y then s x else e y

@[simp] theorem diagonal (e s : G → G) (x : G) : operation e s x x = e x := by
  simp [operation]

theorem satisfies_3272 (e s : G → G) (he : ∀ x, e (e x) = e x)
    (hs : ∀ x, e (s x) = e x) (hne : ∀ x, s x ≠ e x) :
    @Equation3272 G ⟨operation e s⟩ := by
  intro x y
  change operation e s x x = operation e s y (operation e s x (operation e s y y))
  rw [diagonal, diagonal]
  by_cases hxy : e x = e y
  · simp [operation, he, hxy]
  · have hyx : e y ≠ e x := Ne.symm hxy
    simp [operation, he, hs, hxy, hyx, hne]

/-- An equivariant implementation of the construction is FO-definable on a
finite carrier. -/
theorem definableOn_of_split_retraction [Finite G] (M : Magma G)
    (e s : G → G) (he : ∀ x, e (e x) = e x)
    (hs : ∀ x, e (s x) = e x) (hne : ∀ x, s x ≠ e x)
    (hinv : ∀ σ : G → G, Function.Bijective σ →
      (∀ x y, σ (M.op x y) = M.op (σ x) (σ y)) →
      (∀ x, e (σ x) = σ (e x)) ∧ (∀ x, s (σ x) = σ (s x))) :
    Law3272.DefinableOnMagma M := by
  classical
  let N : Magma G := ⟨operation e s⟩
  refine ⟨N, (@Law3272.models_iff G N).mpr (satisfies_3272 e s he hs hne),
    Magma.definable_of_aut_invariant M N.Graph ?_⟩
  intro σ hσ hhom v hv
  obtain ⟨heq, hsq⟩ := hinv σ hσ hhom
  change operation e s (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  change operation e s (v (some 0)) (v (some 1)) = v none at hv
  rw [← hv]
  by_cases hxy : e (v (some 0)) = e (v (some 1))
  · simp only [operation, heq, hσ.injective.eq_iff, if_pos hxy]
  · by_cases hy : v (some 1) = e (v (some 1))
    · simp only [operation, heq, hsq, hσ.injective.eq_iff, if_neg hxy, if_pos hy]
    · simp only [operation, heq, hsq, hσ.injective.eq_iff, if_neg hxy, if_neg hy]

/-- Every self-map of a finite set has a positive idempotent iterate. -/
theorem exists_idempotent_iterate [Finite G] (f : G → G) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, f^[N] (f^[N] x) = f^[N] x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n])
  have hex : ∃ a p : ℕ, 0 < p ∧ f^[a + p] = f^[a] := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j - i, Nat.sub_pos_of_lt hlt, by simpa [Nat.add_sub_of_le hlt.le] using heq.symm⟩
    · exact ⟨j, i - j, Nat.sub_pos_of_lt hgt, by simpa [Nat.add_sub_of_le hgt.le] using heq⟩
  obtain ⟨a, p, hp, hab⟩ := hex
  have hstep (k : ℕ) : f^[a + k + p] = f^[a + k] := by
    rw [show a + k + p = (a + p) + k by omega, Function.iterate_add, hab]
    exact (Function.iterate_add _ _ _).symm
  have hmul (k t : ℕ) : f^[a + k + t * p] = f^[a + k] := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show a + k + (t + 1) * p = a + (k + t * p) + p by simp only [Nat.add_mul, Nat.one_mul]; omega, hstep]
      simpa only [Nat.add_assoc] using ih
  let N := (a + 1) * p
  have haN : a ≤ N := by
    have := Nat.le_mul_of_pos_right (a + 1) hp
    dsimp [N]
    omega
  refine ⟨N, Nat.mul_pos (Nat.succ_pos a) hp, fun x => ?_⟩
  have hperiod := hmul (N - a) (a + 1)
  rw [show a + (N - a) = N by omega] at hperiod
  change f^[N + N] = f^[N] at hperiod
  rw [← Function.iterate_add_apply]
  exact congrFun hperiod x

/-- An equivariant map whose fibers have two elements supplies a canonical
second section after passing to its periodic points. -/
theorem definableOn_of_unique_square_partner [Finite G] (M : Magma G)
    (htwo : ∀ x : G, ∃! y : G, M.op y y = M.op x x ∧ y ≠ x) :
    Law3272.DefinableOnMagma M := by
  classical
  let d : G → G := fun x => M.op x x
  let partner : G → G := fun x => (htwo x).choose
  have hpartner (x : G) : d (partner x) = d x ∧ partner x ≠ x := (htwo x).choose_spec.1
  have hunique (x y : G) (hy : d y = d x ∧ y ≠ x) : y = partner x :=
    (htwo x).choose_spec.2 y hy
  obtain ⟨N, hN, hNN⟩ := exists_idempotent_iterate d
  let e := d^[N]
  let s := partner ∘ e
  have he (x : G) : e (e x) = e x := hNN x
  have hs (x : G) : e (s x) = e x := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    change d^[k + 1] (partner (e x)) = e x
    rw [Function.iterate_succ_apply, (hpartner (e x)).1]
    exact he x
  have hne (x : G) : s x ≠ e x := (hpartner (e x)).2
  apply definableOn_of_split_retraction M e s he hs hne
  intro σ hσ hhom
  have hd (x : G) : d (σ x) = σ (d x) := (hhom x x).symm
  have hiter (n : ℕ) (x : G) : d^[n] (σ x) = σ (d^[n] x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hd, Function.iterate_succ_apply']
  have hp (x : G) : partner (σ x) = σ (partner x) := by
    symm
    apply hunique
    constructor
    · rw [hd, hd, (hpartner x).1]
    · exact hσ.injective.ne (hpartner x).2
  exact ⟨hiter N, fun x => by dsimp [s, e]; rw [hiter, hp]⟩

end SplitRetraction3272
