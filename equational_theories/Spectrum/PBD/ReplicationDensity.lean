import equational_theories.Spectrum.PBD.UniformSeeds
import equational_theories.Spectrum.PBD.AsymptoticArithmetic

/-! Relative density and bounded additive gaps for replication numbers. -/
namespace Spectrum.PBD.Replication
open Classical
variable {k a : ℕ}

/-- The multiplicative mesh of §20.4, starting above any specified threshold. -/
theorem relative_dense (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k})
    (ha : 0 < a) (haC : a ∈ replications k) (haC' : a+1 ∈ replications k) (S : ℕ) :
    ∃ B : ℕ, ∀ x : ℚ, B ≤ x → ∃ r, r ∈ replications k ∧ S ≤ r ∧
      x < r ∧ (a:ℚ)*r ≤ (a+1)*x := by
  let C := replications k
  have hC : DesignClosed C := closed hk
  obtain ⟨A,hA⟩ := HasTD.eventual k
  obtain ⟨B,hB⟩ := HasTD.eventual (a+1)
  obtain ⟨q,hq,hqC⟩ := unbounded hk hu (A+B+a+3)
  let u := a*q+a
  let v := u+1
  have huC : u ∈ C := by
    have h := hC.oneHole (hB q (by omega)) (e := 0) (r := a) (by omega) (by omega)
      (by simpa using hqC) (by simpa using haC) haC haC'
    simpa using h
  have hvC : v ∈ C := by
    have h := hC.oneHole (hB q (by omega)) (e := 0) (r := a+1) (by omega) (by omega)
      (by simpa using hqC) (by simpa using haC') haC haC'
    simpa [v,u,Nat.add_assoc] using h
  have huA : A ≤ u := by dsimp [u]; nlinarith
  have hvA : A ≤ v := by dsimp [v]; omega
  have hu2 : 1 < u := by dsimp [u]; nlinarith
  have huv : u < v := by dsimp [v]; omega
  have hpow : ∀ i, u^i ∈ C := by
    intro i
    induction i with
    | zero => simpa using hC.one_mem
    | succ i ih =>
      simpa [pow_succ] using Replication.mul hk ih huC (hA u huA)
  have hprod : ∀ i j, u^i*v^j ∈ C := by
    intro i j
    induction j with
    | zero => simpa using hpow i
    | succ j ih =>
      simpa [pow_succ,Nat.mul_assoc] using Replication.mul hk ih hvC (hA v hvA)
  obtain ⟨M,hM⟩ := AsymptoticArithmetic.multiplicative_mesh hu2 huv
  refine ⟨M+S+1,?_⟩
  intro x hx
  push_cast at hx
  have hxM : (M:ℚ) ≤ x := by linarith [Nat.cast_nonneg (α := ℚ) S]
  have hxS : (S:ℚ) ≤ x := by linarith [Nat.cast_nonneg (α := ℚ) M]
  have hx0 : (0:ℚ) ≤ x := (Nat.cast_nonneg S).trans hxS
  obtain ⟨i,j,_,hlo,hhi⟩ := hM x hxM
  let r := u^i*v^j
  have hlo' : x < (r:ℚ) := by simpa [r] using hlo
  have hhi' : (u:ℚ)*r ≤ v*x := by simpa [r] using hhi
  have hrS : S ≤ r := by exact_mod_cast hxS.trans hlo'.le
  have hup : (0:ℚ) < u := by exact_mod_cast (by omega : 0 < u)
  have hratio : (a:ℚ)*v ≤ (a+1)*u := by
    have h : a*v ≤ (a+1)*u := by dsimp [u,v]; nlinarith
    exact_mod_cast h
  refine ⟨r,hprod i j,hrS,hlo',?_⟩
  apply (mul_le_mul_iff_right₀ hup).mp
  calc
    (u:ℚ)*(a*r) = a*(u*r) := by ring
    _ ≤ a*(v*x) := mul_le_mul_of_nonneg_left hhi' (by positivity)
    _ = (a*v)*x := by ring
    _ ≤ ((a+1)*u)*x := mul_le_mul_of_nonneg_right hratio hx0
    _ = u*((a+1)*x) := by ring

/-- Wilson §20.5: replication numbers have bounded additive gaps. -/
theorem bounded_gaps (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k})
    (ha : 0 < a) (haC : a ∈ replications k) (haC' : a+1 ∈ replications k) :
    ∃ M, ∀ n, ∃ s, s ∈ replications k ∧ n < s ∧ s ≤ n+M := by
  obtain ⟨A,hA⟩ := HasTD.eventual (a+1)
  obtain ⟨B,hB⟩ := relative_dense hk hu ha haC haC' A
  obtain ⟨M,hM,hMC⟩ := unbounded hk hu ((a+1)*B+1)
  refine ⟨M,AsymptoticArithmetic.bounded_gaps ha hMC (by omega) (by omega) hB ?_⟩
  intro r hr hrA t ht htr
  have h := (closed hk).oneHole (hA r hrA) (e := 0) (by omega) htr
    (by simpa using hr) (by simpa using ht) haC haC'
  simpa using h

end Spectrum.PBD.Replication
