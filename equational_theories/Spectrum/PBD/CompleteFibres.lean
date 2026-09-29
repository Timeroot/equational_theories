import equational_theories.Spectrum.PBD.PeriodConstruction
import equational_theories.Spectrum.PBD.ReplicationTail
import equational_theories.Spectrum.PBD.EventualPeriod
import equational_theories.Spectrum.PBD.FibreArithmetic

/-! Every occupied fibre is complete, using the weighted construction of §21. -/
namespace Spectrum.PBD
open Classical

abbrev UniformOneTail (k : ℕ) : Prop :=
  ∃ U, ∀ n, U ≤ n → n % (k*(k-1)) = 1 → n ∈ designClosure {k}

theorem DesignClosed.uniform_subset {C : Set ℕ} (hC : DesignClosed C) {k : ℕ} (hk : k ∈ C) :
    designClosure {k} ⊆ C := by
  intro n hn
  apply hC
  apply designClosure_mono (show ({k} : Set ℕ) ⊆ C from by
    intro x hx
    have : x = k := hx
    simpa [this] using hk) hn

/-- Every positive seed can be enlarged within any prescribed residue class. -/
theorem DesignClosed.large_residue {C : Set ℕ} (hC : DesignClosed C) {k d u : ℕ}
    (hk : 2 ≤ k) (hkC : k ∈ C) (hU : UniformOneTail k)
    (hd : 0 < d) (hu : 0 < u) (huC : u ∈ C) :
    ∀ N, ∃ w, N ≤ w ∧ w ∈ C ∧ w ≡ u [MOD d] := by
  intro N
  obtain ⟨U,hU⟩ := hU
  obtain ⟨A,hA⟩ := HasTD.eventual u
  let b := k*(k-1)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  let t := U+A+N+1
  let q := b*d*t+1
  have htq : t ≤ q := by
    have h := Nat.le_mul_of_pos_left t (Nat.mul_pos (by omega : 0 < b) hd)
    dsimp [q]
    omega
  have hqb : q%b = 1 := by
    have hdiv : b ∣ b*d*t := dvd_mul_of_dvd_left (dvd_mul_right b d) t
    dsimp [q]
    simp only [Nat.add_mod,Nat.mod_eq_zero_of_dvd hdiv,zero_add,Nat.mod_eq_of_lt hb]
  have hqC : q ∈ C := hC.uniform_subset hkC (hU q (by dsimp [t] at htq; omega) hqb)
  have hD : HasTD u q := hA q (by dsimp [t] at htq; omega)
  refine ⟨u*q,?_,hC.mul_order huC hqC hD,?_⟩
  · have h := Nat.le_mul_of_pos_left q hu
    dsimp [t] at htq
    omega
  · have hqd : q ≡ 1 [MOD d] := by
      dsimp [q,Nat.ModEq]
      simp [Nat.add_mod,Nat.mul_mod]
    simpa using hqd.mul_left u

/-- Wilson's fibre-completion theorem for a period arising from a uniform
k-design in the complete fibre at 1. -/
theorem DesignClosed.complete_fibres {C : Set ℕ} (hC : DesignClosed C) {k v : ℕ}
    (hk : 2 ≤ k) (hkC : k ∈ C) (hU : UniformOneTail k)
    (hv : 3 ≤ v) (hvD : v ∈ designClosure {k}) (hvmod : v % (k*(k-1)) = 1) :
    CompleteFibres C (v-1) := by
  let b := k*(k-1)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hbd : b ∣ v-1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ v)).mp (by
    change 1%b = v%b
    rw [Nat.mod_eq_of_lt hb,hvmod])
  have hvC : v ∈ C := hC.uniform_subset hkC hvD
  intro u₀ hu₀ hu₀C
  obtain ⟨U,hU'⟩ := hU
  obtain ⟨Av,hAv⟩ := HasTD.eventual v
  obtain ⟨Ak,hAk⟩ := HasTD.eventual k
  obtain ⟨u,huN,huC,humod⟩ := hC.large_residue hk hkC ⟨U,hU'⟩ (by omega : 0 < v-1)
    hu₀ hu₀C (Av+Ak+U+k+v+3)
  have hu : 2 ≤ u := by omega
  have D₁ : Nonempty (OneGroupDesign C (u-1) (v-1) u) := by
    obtain ⟨T⟩ := hAv u (by omega)
    simpa using T.localized_oneGroup (e := 0) (by omega) hvC (by simpa using huC) (by omega) (by omega)
  have D₀ : Nonempty (OneGroupDesign C (u-1) (v-1) (u-1)) := by
    obtain ⟨T⟩ := hAv (u-1) (by omega)
    have huC' : u-1+1 ∈ C := by rwa [Nat.sub_add_cancel (by omega : 1 ≤ u)]
    simpa using T.localized_oneGroup (e := 1) (by omega) hvC huC' (by omega) (by omega)
  obtain ⟨A,hA⟩ := HasTD.eventual (u+1)
  let M := U+A+(u-1)*v+2
  have hM : (u-1)*((v-1)+1) ≤ M := by rw [Nat.sub_add_cancel (by omega : 1 ≤ v)]; dsimp [M]; omega
  obtain ⟨N,hN⟩ := fibre_decompose hu (by omega : 2 ≤ v-1) hb hbd hM (by dsimp [M]; omega)
  refine ⟨N,?_⟩
  intro w hw hwmod
  obtain ⟨r,q,hrM,hrq,hqM,hqmod,heq⟩ := hN w hw (hwmod.trans humod.symm)
  have hrU : U ≤ r := by dsimp [M] at hrM; omega
  have hqU : U ≤ q := by dsimp [M] at hqM; omega
  have hqD : q ∈ designClosure {k} := hU' q hqU hqmod
  have fill₀ : q*(u-1)+1 ∈ C :=
    hC.inflate_uniform hkC (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ u)]) hqD
      (hAk (u-1) (by omega))
  have fill (t : ℕ) (ht : U ≤ t) : t*(v-1)+1 ∈ C := by
    apply hC.uniform_subset hkC
    apply hU'
    · have h := Nat.le_mul_of_pos_right t (by omega : 0 < v-1)
      omega
    · have hdvd : b ∣ t*(v-1) := hbd.mul_left t
      change (t*(v-1)+1)%b = 1
      simp only [Nat.add_mod,Nat.mod_eq_zero_of_dvd hdvd,zero_add,Nat.mod_eq_of_lt hb]
  have h := hC.period_construction hu (by omega) hrq D₀ D₁
    (hA q (by dsimp [M] at hqM; omega)) fill₀ (fill r hrU) (fill q hqU)
  have heq' : (v-1)*r+(u-1)*q*v+1 = w := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ v)] using heq
  exact heq' ▸ h

end Spectrum.PBD
