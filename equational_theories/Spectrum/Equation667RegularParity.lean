import equational_theories.Spectrum.Equation667GroupConstructions
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The elementary parity obstruction to a regular group of automorphisms
at orders two modulo four. This is the necessary, easy special case of the
complete-mapping obstruction; no general Hall--Paige theorem is used. -/
namespace Spectrum.E667.RegularParity
open scoped BigOperators
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

/-- A complete mapping makes the product of every one-dimensional character
over the group equal to one. -/
theorem character_product {C : Type*} [CommGroup C] (χ : G →* C)
    (f : G → G) (hf : Function.Bijective f)
    (hd : Function.Bijective (fun x => x⁻¹ * f x)) : (∏ x, χ x) = 1 := by
  calc
    (∏ x, χ x) = ∏ x, χ (x⁻¹ * f x) := (hd.prod_comp χ).symm
    _ = (∏ x, χ x)⁻¹ * ∏ x, χ (f x) := by
      simp only [map_mul, map_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = 1 := by rw [hf.prod_comp χ, inv_mul_cancel]

/-- A nontrivial sign character has equally many values of each sign. -/
theorem sign_product (χ : G →* ℤˣ) (a : G) (ha : χ a = -1)
    (hn : Fintype.card G % 4 = 2) : (∏ x, χ x) = -1 := by
  classical
  let N := (Finset.univ.filter (fun x : G => χ x = -1)).card
  have he := MonoidHom.card_fiber_eq_of_mem_range χ
    (x := (-1 : ℤˣ)) (y := 1) ⟨a,ha⟩ ⟨1,χ.map_one⟩
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun x : G => χ x = -1)
  have hnot : (Finset.univ.filter (fun x : G => ¬ χ x = -1)) =
      Finset.univ.filter (fun x : G => χ x = 1) := by
    ext x
    rcases Int.units_eq_one_or (χ x) with hh | hh <;> simp [hh]
  rw [hnot, ← he] at hc
  have hn' : 2 * N = Fintype.card G := by simpa only [N, two_mul, Finset.card_univ] using hc
  have ho : Odd N := ⟨N/2, by omega⟩
  calc
    (∏ x, χ x) = ∏ x : G, if χ x = -1 then (-1 : ℤˣ) else 1 := by
      apply Finset.prod_congr rfl
      intro x _
      rcases Int.units_eq_one_or (χ x) with hh | hh <;> simp [hh]
    _ = (-1 : ℤˣ)^N := by
      simp [Finset.prod_ite, N]
      rfl
    _ = -1 := ho.neg_one_pow

/-- In the regular permutation action, an element of order two has negative
sign when the carrier has order two modulo four. -/
theorem exists_negative_sign (hn : Fintype.card G % 4 = 2) :
    ∃ χ : G →* ℤˣ, ∃ a : G, χ a = -1 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card (G := G) 2
    (Nat.dvd_of_mod_eq_zero (by omega))
  have ha2 : a*a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hane : a ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at ha
    omega
  let r : G →* Equiv.Perm G := MulAction.toPermHom G G
  let χ : G →* ℤˣ := Equiv.Perm.sign.comp r
  refine ⟨χ,a,?_⟩
  have hr : r a ^ 2 = 1 := by rw [← map_pow, pow_two, ha2, map_one]
  haveI : IsEmpty (Function.fixedPoints (r a)) := ⟨fun x => by
    have hh : a * x.val = x.val := x.property
    exact hane (mul_right_cancel (hh.trans (one_mul x.val).symm))⟩
  have hz : Fintype.card (Function.fixedPoints (r a)) = 0 := Fintype.card_eq_zero_iff.mpr inferInstance
  have hh := Equiv.Perm.sign_of_pow_two_eq_one hr
  rw [hz] at hh
  have ho : Odd (Fintype.card G / 2) := ⟨Fintype.card G / 4, by omega⟩
  simpa only [χ, MonoidHom.comp_apply, Nat.sub_zero,
    ho.neg_one_pow] using hh

/-- No complete mapping exists at an order two modulo four. -/
theorem no_complete_mapping (hn : Fintype.card G % 4 = 2)
    (f : G → G) (hf : Function.Bijective f) :
    ¬ Function.Bijective (fun x => x⁻¹ * f x) := by
  intro hd
  obtain ⟨χ,a,ha⟩ := exists_negative_sign (G := G) hn
  have hh := (character_product χ f hf hd).symm.trans (sign_product χ a ha hn)
  have hval := congrArg (fun u : ℤˣ => (u : ℤ)) hh
  norm_num at hval

/-- In particular no E667 regular-group construction can have order 2 mod 4.
This excludes this construction family at the open orders 30, 102, and 174,
independently of the chosen group or diagonal behavior. -/
theorem no_regular_model (hn : Fintype.card G % 4 = 2) (f : G → G) :
    ¬ @Equation667 G ⟨GroupConstructions.regularOp f⟩ := by
  intro h
  obtain ⟨hf,hd⟩ := GroupConstructions.regular_permutations f h
  exact no_complete_mapping hn f hf hd

/-- The operation need not initially be supplied as a profile: equivariance
under all left translations already supplies the required representation. -/
theorem no_equivariant_model (hn : Fintype.card G % 4 = 2)
    (q : G → G → G) (he : ∀ g x y, q (g*x) (g*y) = g*q x y) :
    ¬ @Equation667 G ⟨q⟩ := by
  have hq : q = GroupConstructions.regularOp (q 1) := by
    funext x y
    exact GroupConstructions.regular_representation q he x y
  rw [hq]
  exact no_regular_model hn (q 1)

spectrum_assert no_complete_mapping complete
spectrum_assert no_regular_model complete
spectrum_assert no_equivariant_model complete
end
end Spectrum.E667.RegularParity
