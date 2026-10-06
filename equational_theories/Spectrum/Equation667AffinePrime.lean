import equational_theories.Spectrum.Equation667AffineCyclic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Coset.Card

/-! A prime with no root of the E667 polynomial cannot occur to the first
power in the order of an affine E667 algebra. -/
namespace Spectrum.E667.AffineStructure
variable {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]

private theorem map_scalar (f : ZMod p →+ A) (k u : ZMod p) :
    f (k*u) = k.val • f u := by
  rw [← map_nsmul]
  congr 1
  simp [nsmul_eq_mul]

private theorem map_at_one (f : ZMod p →+ A) (u : ZMod p) : f u = u.val • f 1 := by
  simpa only [mul_one] using map_scalar f u 1

private theorem map_injective (f : ZMod p →+ A) (hf : f 1 ≠ 0) : Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro u hu
  by_contra hn
  apply hf
  have hh := map_scalar f u⁻¹ u
  rw [inv_mul_cancel₀ hn, hu, nsmul_zero] at hh
  exact hh

private theorem independent_maps (f k : ZMod p →+ A) (hf : f 1 ≠ 0)
    (hk : ∀ u, k 1 ≠ f u) : p^2 ∣ Nat.card A := by
  let F : (ZMod p × ZMod p) →+ A := {
    toFun := fun x => f x.1+k x.2
    map_zero' := by simp
    map_add' := fun x y => by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel }
  have hi : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    rintro ⟨u,v⟩ hh
    change f u+k v=0 at hh
    by_cases hv : v = 0
    · subst v
      rw [map_zero, add_zero] at hh
      exact Prod.ext ((map_injective f hf) (hh.trans (map_zero f).symm)) rfl
    · exfalso
      have he := congrArg (fun x : A => v⁻¹.val • x) hh
      change (v⁻¹).val • (f u+k v) = (v⁻¹).val • (0 : A) at he
      rw [nsmul_add, ← map_scalar, ← map_scalar, inv_mul_cancel₀ hv, nsmul_zero] at he
      apply hk (-(v⁻¹*u))
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_right he
  have hd := AddSubgroup.card_dvd_of_injective F hi
  simpa [pow_two] using hd

private def primeMap (a : A) (ha : (p : ℕ) • a = 0) : ZMod p →+ A :=
  ZMod.lift p ⟨{
    toFun := fun z => z • a
    map_zero' := zero_zsmul a
    map_add' := fun x y => add_zsmul a x y }, by
      change (p : ℤ) • a = 0
      rw [natCast_zsmul]
      exact ha⟩

private theorem primeMap_one (a : A) (ha : (p : ℕ) • a = 0) : primeMap a ha 1 = a := by
  have hh := ZMod.lift_coe p (⟨{
    toFun := fun z => z • a
    map_zero' := zero_zsmul a
    map_add' := fun x y => add_zsmul a x y }, by
      change (p : ℤ) • a = 0; rw [natCast_zsmul]; exact ha⟩) 1
  change primeMap a ha ((1 : ℤ) : ZMod p) = (1 : ℤ) • a at hh
  simpa only [Int.cast_one, one_zsmul] using hh

/-- If P has no root modulo p, then a nonzero p-torsion point and its B-image
are independent. Their subgroup has order p². -/
theorem prime_square_dvd_of_no_root [Finite A] (g : AddMonoid.End A) (hp : P g = 0)
    (hd : p ∣ Nat.card A) (hr : ∀ t : ZMod p, t^8-t^6-t^4-1 ≠ 0) : p^2 ∣ Nat.card A := by
  obtain ⟨a,ha⟩ := exists_prime_addOrderOf_dvd_card' p hd
  have haP : p • a = 0 := by rw [← ha]; exact addOrderOf_nsmul_eq_zero a
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, addOrderOf_zero] at ha
    exact (Fact.out : p.Prime).ne_one ha.symm
  let f := primeMap a haP
  have hf1 : f 1 = a := primeMap_one a haP
  have hfi := map_injective f (hf1 ▸ ha0)
  apply independent_maps f (g.comp f) (hf1 ▸ ha0)
  intro t ht
  have hga : g a = f t := by simpa only [AddMonoidHom.comp_apply, hf1] using ht
  have intertwine (u : ZMod p) : g (f u) = f (u*t) := by
    rw [map_at_one f u, hf1, map_nsmul, hga, ← map_scalar]
  have powers (n : ℕ) : (g^n) a = f (t^n) := by
    induction n with
    | zero => rw [pow_zero, pow_zero, end_one_apply, hf1]
    | succ n ih => rw [pow_succ', end_mul_apply, ih, intertwine, pow_succ]
  have hh := congrArg (fun H : AddMonoid.End A => H a) hp
  have he : P g a = f (t^8-t^6-t^4-1) := by
    simp only [P, end_sub_apply, end_one_apply, powers, map_sub, hf1]
  change P g a = 0 at hh
  rw [he] at hh
  exact hr t (hfi (hh.trans (map_zero f).symm))

theorem affine_prime_square_dvd [Finite A] (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) (hd : p ∣ Nat.card A)
    (hr : ∀ t : ZMod p, t^8-t^6-t^4-1 ≠ 0) : p^2 ∣ Nat.card A :=
  prime_square_dvd_of_no_root g ((full_law_iff f g c).mp h).2.1 hd hr

theorem thirty_one_dvd_implies_square_dvd [Finite A] (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) (hd : 31 ∣ Nat.card A) : 31^2 ∣ Nat.card A := by
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  exact affine_prime_square_dvd f g c h hd no_root_thirty_one

theorem forty_seven_dvd_implies_square_dvd [Finite A] (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) (hd : 47 ∣ Nat.card A) : 47^2 ∣ Nat.card A := by
  letI : Fact (Nat.Prime 47) := ⟨by decide⟩
  exact affine_prime_square_dvd f g c h hd no_root_forty_seven

spectrum_assert thirty_one_dvd_implies_square_dvd complete
spectrum_assert forty_seven_dvd_implies_square_dvd complete
spectrum_assert prime_square_dvd_of_no_root complete
end Spectrum.E667.AffineStructure
