import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Sylow
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Cardinalities of finite Gaussian modules

On an odd-order group, if inversion is the square of a permutation, its sign
is positive. Since inversion fixes only the identity, the order is 1 modulo 4.
Apply this observation to each characteristic Sylow subgroup of an abelian
group with an automorphism whose square is inversion.
-/

namespace Spectrum.GaussianCardinality
open Equiv

theorem odd_card_mod_four {G : Type*} [Group G] [Fintype G]
    (σ : Perm G) (hs : ∀ x, σ (σ x) = x⁻¹) (ho : Odd (Fintype.card G)) :
    Fintype.card G % 4 = 1 := by
  classical
  let ν : Perm G := ⟨Inv.inv, Inv.inv, inv_inv, inv_inv⟩
  have hn : ν ^ 2 = 1 := by ext x; simp [ν, pow_two]
  have hσ : σ ^ 2 = ν := by ext x; exact hs x
  have hsign : Perm.sign ν = 1 := by rw [← hσ, map_pow]; simp
  have hfix {x : G} (hx : ν x = x) : x = 1 := by
    have hx2 : x ^ 2 = 1 := by
      change x⁻¹ = x at hx
      calc x ^ 2 = x⁻¹ * x := by rw [pow_two, hx]
           _ = 1 := inv_mul_cancel x
    have hc : (Nat.card G).Coprime 2 := by
      simpa only [Nat.card_eq_fintype_card] using ho.coprime_two_right
    apply hc.pow_left_bijective.injective
    simpa only [one_pow] using hx2
  have hfixed : Fintype.card (Function.fixedPoints ν) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨1, by simp [Function.IsFixedPt, ν]⟩, ?_⟩
    intro x
    exact Subtype.ext (hfix x.property)
  have hp := Perm.sign_of_pow_two_eq_one hn
  rw [hsign, hfixed] at hp
  have he : Even ((Fintype.card G - 1) / 2) := by
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hp.symm
  rw [even_iff_two_dvd] at he
  rw [Nat.odd_iff] at ho
  omega

theorem card_sum_two_squares {G : Type*} [CommGroup G] [Fintype G]
    (J : G ≃* G) (hJ : ∀ x, J (J x) = x⁻¹) :
    ∃ a b : ℕ, Fintype.card G = a^2 + b^2 := by
  classical
  apply Nat.eq_sq_add_sq_iff.mpr
  intro p hp hp4
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  let P : Sylow p G := default
  letI : Fintype P := Fintype.ofFinite P
  haveI : P.Characteristic := P.characteristic_of_normal inferInstance
  have hm : ∀ x : G, x ∈ (P : Subgroup G) → J x ∈ (P : Subgroup G) :=
    Subgroup.characteristic_iff_le_comap.mp inferInstance J
  let f : P → P := fun x => ⟨J x.val, hm x.val x.property⟩
  have hi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (J.injective (congrArg Subtype.val he))
  let σ : Perm P := Equiv.ofBijective f hi.bijective_of_finite
  have hs (x : P) : σ (σ x) = x⁻¹ := by
    apply Subtype.ext
    exact hJ x.val
  have hc : Fintype.card P = p ^ (Fintype.card G).factorization p := by
    simpa only [Nat.card_eq_fintype_card] using P.card_eq_multiplicity
  have hop : Odd p := by rw [Nat.odd_iff]; omega
  have ho : Odd (Fintype.card P) := by rw [hc]; exact hop.pow
  have hr := odd_card_mod_four σ hs ho
  rw [hc, Nat.pow_mod, hp4] at hr
  have he : Even ((Fintype.card G).factorization p) := by
    rw [Nat.even_iff]
    have hpow : ∀ k : ℕ, 3 ^ k % 4 = if k % 2 = 0 then 1 else 3 := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ, Nat.mul_mod, ih]
        split_ifs <;> simp_all <;> omega
    rw [hpow] at hr
    split_ifs at hr with hk
    · exact hk
    · contradiction
  simpa only [Nat.factorization_def, (Nat.prime_of_mem_primeFactors hp), if_pos] using he

end Spectrum.GaussianCardinality
