import equational_theories.Spectrum.Equation501.Parity
import equational_theories.Spectrum.InvolutionRoots
import Mathlib.Data.ZMod.Basic

/-! The exact E501 spectrum is the positive orders congruent to 0 or 1 modulo 4.
The upper bound uses permutation signs; independent square roots of abelian-group
reflections construct every allowed order. See `docs/501_finite_spectrum_theorem.md`.
-/

namespace Spectrum.E501

section Reflections
variable {G : Type*} [AddCommGroup G]

def reflection (a : G) : Equiv.Perm G where
  toFun y := -a - y
  invFun y := -a - y
  left_inv y := by dsimp; abel
  right_inv y := by dsimp; abel

theorem reflection_twice (a y : G) : reflection a (reflection a y) = y := by
  change -a - (-a - y) = y
  abel

/-- Independent square roots of the reflection rows give E501. -/
theorem model_of_roots [Fintype G]
    (h : ∀ a : G, ∃ r : G → G, ∀ y, r (r y) = -a - y) :
    Law501.HasModel (Fintype.card G) := by
  choose p hp using h
  let M : Magma G := ⟨p⟩
  apply Law.MagmaLaw.hasModel_of_fintype M
  apply (@Law501.models_iff G M).mpr
  intro x y
  change x = p y (p y (p x (p x y)))
  rw [hp, hp]
  abel
end Reflections

set_option backward.isDefEq.respectTransparency false in
/-- Signs of product permutations, with each factor repeated once per opposite fiber. -/
theorem sign_prod {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : Equiv.Perm A) (g : Equiv.Perm B) :
    Equiv.Perm.sign (Equiv.prodCongr f g) =
      Equiv.Perm.sign f ^ Fintype.card B * Equiv.Perm.sign g ^ Fintype.card A := by
  have he : Equiv.prodCongr f g =
      Equiv.prodCongrLeft (fun _ : B => f) * Equiv.prodCongrRight (fun _ : A => g) := by
    ext x <;> rfl
  rw [he, Equiv.Perm.sign_mul, Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight]
  simp

/-- Every order congruent to one modulo four, using the cyclic group. -/
theorem model_odd (k : ℕ) : Law501.HasModel (4 * k + 1) := by
  classical
  letI : NeZero (4 * k + 1) := ⟨by omega⟩
  let G := ZMod (4 * k + 1)
  letI : LinearOrder G := LinearOrder.lift' (Fintype.equivFin G) (Fintype.equivFin G).injective
  letI : DecidableEq G := LinearOrder.toDecidableEq
  have hm : Law501.HasModel (Fintype.card G) := model_of_roots fun a => by
    let c : G := (2 * k + 1 : ℕ)
    have hc : (2 : G) * c = 1 := by
      have hn := ZMod.natCast_self (4 * k + 1)
      dsimp [c, G]
      push_cast at hn ⊢
      linear_combination hn
    have unique_fixed (y : G) (hy : reflection a y = y) : y = -c * a := by
      change -a - y = y at hy
      have hd : (2 : G) * y = -a := by linear_combination -hy
      calc
        y = ((2 : G) * c) * y := by rw [hc, one_mul]
        _ = c * ((2 : G) * y) := by ring
        _ = c * (-a) := by rw [hd]
        _ = -c * a := by ring
    have hfixed : reflection a (-c * a) = -c * a := by
      change -a - (-c * a) = -c * a
      linear_combination a * hc
    have hfcard : Fintype.card (InvolutionRoots.Fixed (reflection a)) = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      exact ⟨⟨-c * a, hfixed⟩, fun y => Subtype.ext (unique_fixed y y.property)⟩
    have hcard := InvolutionRoots.card_decompose (reflection a) (reflection_twice a)
    simp only [hfcard] at hcard
    have hgcard : Fintype.card G = 4 * k + 1 := ZMod.card _
    rw [hgcard] at hcard
    have he : Even (Fintype.card (InvolutionRoots.Asc (reflection a))) := by
      rw [Nat.even_iff]
      omega
    obtain ⟨r, hr⟩ := InvolutionRoots.exists_root_of_even (reflection a) (reflection_twice a) he
    exact ⟨r, hr⟩
  simpa [G, ZMod.card] using hm

set_option backward.isDefEq.respectTransparency false in
/-- Every positive multiple of four. Both cyclic factors have even order, so
all product reflection permutations are even. -/
theorem model_even (k : ℕ) (hk : 0 < k) : Law501.HasModel (4 * k) := by
  classical
  letI : NeZero (2 * k) := ⟨by omega⟩
  let G := ZMod 2 × ZMod (2 * k)
  letI : LinearOrder G := LinearOrder.lift' (Fintype.equivFin G) (Fintype.equivFin G).injective
  letI : DecidableEq G := LinearOrder.toDecidableEq
  have hm : Law501.HasModel (Fintype.card G) := model_of_roots fun a => by
    have heq : reflection a = Equiv.prodCongr (reflection a.1) (reflection a.2) := by
      ext y <;> rfl
    have he : Equiv.Perm.sign (reflection a) = 1 := by
      rw [heq]
      trans Equiv.Perm.sign (reflection a.1) ^ Fintype.card (ZMod (2 * k)) *
        Equiv.Perm.sign (reflection a.2) ^ Fintype.card (ZMod 2)
      · convert sign_prod (reflection a.1) (reflection a.2) using 1
        congr 4
        exact Subsingleton.elim _ _
      · simp [ZMod.card, pow_mul, pow_two, Int.units_mul_self]
    obtain ⟨r, hr⟩ := InvolutionRoots.exists_root_of_sign (reflection a) (reflection_twice a) he
    exact ⟨r, hr⟩
  convert hm using 1
  simp [G, ZMod.card, Fintype.card_prod]
  omega

end E501

/-- All finite cardinalities, allowing the empty model. -/
theorem hasModel_501_iff (n : ℕ) : Law501.HasModel n ↔ n % 4 = 0 ∨ n % 4 = 1 := by
  constructor
  · rintro ⟨M, hM⟩
    letI := M
    simpa using E501.residue ((@Law501.models_iff (Fin n) M).mp hM)
  · intro hn
    rcases hn with hn | hn
    · by_cases hz : n = 0
      · subst n; exact Law501.hasModel_zero
      have he : n = 4 * (n / 4) := by omega
      rw [he]
      exact E501.model_even _ (by omega)
    · have he : n = 4 * (n / 4) + 1 := by omega
      rw [he]
      exact E501.model_odd _

/-- The complete positive finite spectrum of E501. -/
theorem exact_501 : Law501.spectrum = residues 4 {0, 1} ∅ := by
  ext n
  simp [Law.MagmaLaw.spectrum, residues, hasModel_501_iff]

/-- info: 'Spectrum.exact_501' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_501
end Spectrum
