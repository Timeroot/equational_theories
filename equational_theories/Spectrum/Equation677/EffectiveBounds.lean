import equational_theories.Spectrum.Equation677.DesignWitnesses
import equational_theories.Spectrum.PBD.EffectiveSieve

/-! Reducing a numerical E677 tail to finite integer and model certificates.
No numerical tail is asserted in this file without those certificates. -/
namespace Spectrum.E677.EffectiveBounds
open Classical Law Law.MagmaLaw PBD.EffectiveSieve

/-- Hole orders in a fixed residue class, together with integer weights that
exclude simultaneous covering by the forbidden prime divisibilities. -/
structure HoleCertificate (R : ℕ) where
  indices : Fin 480 → Finset ℕ
  weight : Fin 480 → ℕ → ℕ
  cap : Fin 480 → ℕ → ℕ
  orders : ∀ t j, j ∈ indices t → 0 < 480*j+t.val ∧ 480*j+t.val ≤ R
  models : ∀ t j, j ∈ indices t → Model (Fin (480*j+t.val))
  bounds : ∀ t p, p ∈ primes80 → ∀ r,
    (∑ j ∈ indices t, if j % p = r then weight t j else 0) ≤ cap t p
  enough : ∀ t, (∑ p ∈ primes80, cap t p) < ∑ j ∈ indices t, weight t j

/-- Every sufficiently large target has a decomposition using one of the
finite certified holes. The full-group order is odd and at least `R`. -/
theorem HoleCertificate.decompose {R n : ℕ} (S : HoleCertificate R)
    (hR : 480 ≤ R) (hn : 81*R < n) :
    ∃ q r, R ≤ q ∧ q < n ∧ r ≤ q ∧ 80*q+r=n ∧
      q % 2 = 1 ∧ PBD.HasTD 81 q ∧ Model (Fin r) := by
  let t : Fin 480 := ⟨(n+400)%480, Nat.mod_lt _ (by decide)⟩
  let a := (n-t.val)/80
  let q (j : ℕ) := a-6*j
  have ht : t.val = (n+400)%480 := rfl
  have ha : 80*a+t.val = n ∧ a%6=1 := by dsimp [a]; omega
  have hp (j : ℕ) (hj : j ∈ S.indices t) : q j+6*j=a := by
    have hr := S.orders t j hj
    dsimp [q]
    omega
  obtain ⟨j,hj,_,havoid⟩ := affine_avoid (S.indices t) primes80 (S.weight t)
    id q (S.cap t) a 6 hp primes80_coprime (S.bounds t) (S.enough t)
  have hr := S.orders t j hj
  have hq6 : q j % 6 = 1 := by have := hp j hj; omega
  have hqR : R ≤ q j := by have := hp j hj; omega
  refine ⟨q j,480*j+t.val,hqR,?_,?_,?_,?_,PBD.EffectiveSieve.td81 (by omega) hq6 havoid,
    S.models t j hj⟩ <;> have := hp j hj <;> omega

private theorem model_of_hasModel {n : ℕ} (h : Law677.HasModel n) : Model (Fin n) := by
  obtain ⟨m,hm⟩ := h
  exact ⟨m.op, fun x y => ((@Law677.models_iff (Fin n) m).mp hm x y).symm, by simp⟩

/-- Once the hole certificate is checked, only a finite initial interval and
a finite interval of odd orders are needed. This avoids multiplying the full
cutoff by the number of transversal groups. -/
theorem tail {C R : ℕ} (S : HoleCertificate R) (hR : 480 ≤ R)
    (base : ∀ n, C ≤ n → n ≤ 81*R → Law677.HasModel n)
    (odd : ∀ q, R ≤ q → q < C → q%2=1 → Law677.HasModel q) :
    ∀ n, C ≤ n → Law677.HasModel n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hb : n ≤ 81*R
    · exact base n hn hb
    obtain ⟨q,r,hq,hqn,hr,he,hodd,hD,hM⟩ := S.decompose hR (by omega : 81*R < n)
    have hqM : Law677.HasModel q := by
      by_cases hc : q < C
      · exact odd q hq hc hodd
      · exact ih q hqn (by omega)
    rw [← he]
    exact hasTD_models hD hr (model_of_hasModel hqM) hM idem80 idem81

end Spectrum.E677.EffectiveBounds

/-- info: 'Spectrum.E677.EffectiveBounds.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.E677.EffectiveBounds.tail
