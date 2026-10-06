import equational_theories.Spectrum.Equation667AffineStructure
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Cyclic affine E667 models require a root of the E667 polynomial modulo
the group order. In particular the known models of prime orders 31 and 47
cannot be affine over any abelian group. -/
namespace Spectrum.E667.AffineStructure

private theorem scalar {n : ℕ} (g : AddMonoid.End (ZMod n)) (x : ZMod n) : g x = x*g 1 := by
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective x
  calc
    g (z : ZMod n) = g (z • (1 : ZMod n)) := by simp
    _ = z • g 1 := map_zsmul g z 1
    _ = (z : ZMod n)*g 1 := by simp [zsmul_eq_mul]

theorem zmod_root {n : ℕ} (g : AddMonoid.End (ZMod n)) (hp : P g = 0) :
    (g 1)^8-(g 1)^6-(g 1)^4-1 = 0 := by
  have evalpow (k : ℕ) : (g^k) 1 = (g 1)^k := by
    induction k with
    | zero => rw [pow_zero, pow_zero, end_one_apply]
    | succ k ih =>
      rw [pow_succ', end_mul_apply, scalar g _, ih, pow_succ]
  have he : P g 1 = (g 1)^8-(g 1)^6-(g 1)^4-1 := by
    simp only [P, end_sub_apply, end_one_apply, evalpow]
  rw [← he, hp]
  rfl

/-- Exact existence criterion on a cyclic additive carrier. The reverse
construction uses multiplication by a root and zero affine constant. -/
theorem cyclic_affine_iff (n : ℕ) :
    (∃ f g : AddMonoid.End (ZMod n), ∃ c : ZMod n, @Equation667 (ZMod n) ⟨op f g c⟩) ↔
      ∃ t : ZMod n, t^8-t^6-t^4-1 = 0 := by
  constructor
  · rintro ⟨f,g,c,h⟩
    exact ⟨g 1,zmod_root g ((full_law_iff f g c).mp h).2.1⟩
  · rintro ⟨t,ht⟩
    let g : AddMonoid.End (ZMod n) := {
      toFun := fun x => x*t
      map_zero' := zero_mul t
      map_add' := fun x y => add_mul x y t }
    have hp : P g = 0 := by
      apply AddMonoidHom.ext
      intro x
      simp only [P, pow_succ, pow_zero]
      change (((((((x*t)*t)*t)*t)*t)*t)*t)*t - (((((x*t)*t)*t)*t)*t)*t - (((x*t)*t)*t)*t - x = 0
      linear_combination x * ht
    exact ⟨-(g^3),g,0,(law_iff g 0).mpr ⟨hp,map_zero _⟩⟩

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def transportEnd (e : A ≃+ B) (f : AddMonoid.End A) : AddMonoid.End B :=
  e.toAddMonoidHom.comp (f.comp e.symm.toAddMonoidHom)

theorem transport_law (e : A ≃+ B) (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) :
    @Equation667 B ⟨op (transportEnd e f) (transportEnd e g) (e c)⟩ := by
  have he (x y : A) :
      e (op f g c x y) = op (transportEnd e f) (transportEnd e g) (e c) (e x) (e y) := by
    change e (f x+g y+c) = e (f (e.symm (e x)))+e (g (e.symm (e y)))+e c
    rw [e.symm_apply_apply, e.symm_apply_apply, map_add, map_add]
  intro x y
  obtain ⟨a,rfl⟩ := e.surjective x
  obtain ⟨b,rfl⟩ := e.surjective y
  simpa only [he] using congrArg e (h a b)

/-- A necessary root criterion for every cyclic affine model, independent
of the chosen coordinates or the affine constant. -/
theorem cyclic_root [IsAddCyclic A] (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) :
    ∃ t : ZMod (Nat.card A), t^8-t^6-t^4-1 = 0 := by
  let e := (zmodAddCyclicAddEquiv (G := A) inferInstance).symm
  have hh := (full_law_iff _ _ _).mp (transport_law e f g c h)
  exact ⟨transportEnd e g 1, zmod_root _ hh.2.1⟩

/-- At prime order, every abelian group is cyclic. -/
theorem prime_root {p : ℕ} [Fact p.Prime] (hc : Nat.card A = p)
    (f g : AddMonoid.End A) (c : A) (h : @Equation667 A ⟨op f g c⟩) :
    ∃ t : ZMod p, t^8-t^6-t^4-1 = 0 := by
  letI : IsAddCyclic A := isAddCyclic_of_prime_card hc
  have hh := cyclic_root f g c h
  rw [hc] at hh
  exact hh

theorem no_root_three : ∀ t : ZMod 3, t^8-t^6-t^4-1 ≠ 0 := by decide +kernel
theorem no_root_thirty_one : ∀ t : ZMod 31, t^8-t^6-t^4-1 ≠ 0 := by decide +kernel
theorem no_root_forty_seven : ∀ t : ZMod 47, t^8-t^6-t^4-1 ≠ 0 := by decide +kernel

theorem not_affine_prime31 (hc : Nat.card A = 31) (f g : AddMonoid.End A) (c : A) :
    ¬ @Equation667 A ⟨op f g c⟩ := by
  intro h
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  obtain ⟨t,ht⟩ := prime_root hc f g c h
  exact no_root_thirty_one t ht

theorem not_affine_prime47 (hc : Nat.card A = 47) (f g : AddMonoid.End A) (c : A) :
    ¬ @Equation667 A ⟨op f g c⟩ := by
  intro h
  letI : Fact (Nat.Prime 47) := ⟨by decide⟩
  obtain ⟨t,ht⟩ := prime_root hc f g c h
  exact no_root_forty_seven t ht

/-- Cyclic affine root obstructions pass from a divisor to the whole order. -/
theorem root_of_dvd {m n : ℕ} (hd : m ∣ n)
    (hr : ∃ t : ZMod n, t^8-t^6-t^4-1 = 0) :
    ∃ t : ZMod m, t^8-t^6-t^4-1 = 0 := by
  obtain ⟨t,ht⟩ := hr
  let φ : ZMod n →+* ZMod m := ZMod.castHom hd (ZMod m)
  refine ⟨φ t,?_⟩
  have hh := congrArg φ ht
  simpa only [map_sub, map_pow, map_one, map_zero] using hh

/-- A cyclic abelian carrier whose order is divisible by three has no affine
E667 operation, even when the order is divisible by nine. -/
theorem not_cyclic_affine_three [IsAddCyclic A] (hd : 3 ∣ Nat.card A)
    (f g : AddMonoid.End A) (c : A) : ¬ @Equation667 A ⟨op f g c⟩ := by
  intro h
  obtain ⟨t,ht⟩ := root_of_dvd hd (cyclic_root f g c h)
  exact no_root_three t ht

spectrum_assert cyclic_affine_iff complete
spectrum_assert not_cyclic_affine_three complete
spectrum_assert cyclic_root complete
spectrum_assert not_affine_prime31 complete
spectrum_assert not_affine_prime47 complete
end Spectrum.E667.AffineStructure
