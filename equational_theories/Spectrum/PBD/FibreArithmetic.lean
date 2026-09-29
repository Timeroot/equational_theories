import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! Arithmetic for the complete-fibre construction in Wilson's §21. -/
namespace Spectrum.PBD

/-- Express a sufficiently large integer in one fibre in the form required
by the weighted design, with the second parameter 1 modulo a prescribed
 divisor of the fibre period. -/
theorem fibre_decompose {u d b M : ℕ} (hu : 2 ≤ u) (hd : 2 ≤ d)
    (hb : 2 ≤ b) (hbd : b ∣ d) (hM : (u-1)*(d+1) ≤ M) (_hMp : 1 ≤ M) :
    ∃ N, ∀ w, N ≤ w → w ≡ u [MOD d] →
      ∃ r q, M ≤ r ∧ r ≤ q ∧ M ≤ q ∧ q%b = 1 ∧
        d*r+(u-1)*q*(d+1)+1 = w := by
  let B := (u-1)*(d+1)
  have hB : 0 < B := Nat.mul_pos (by omega) (by omega)
  let L := M+(u-1)+B*M
  refine ⟨u+d*L,?_⟩
  intro w hw hmod
  have huw : u ≤ w := by omega
  obtain ⟨t,ht⟩ := (Nat.modEq_iff_exists_eq_add huw).mp hmod.symm
  have hLt : L ≤ t := by nlinarith only [hw,ht,hd]
  let m := (t-L)/B
  let s := (t-L)%B
  let r := M+s
  let q := (m+M)*d+1
  have hs : s < B := Nat.mod_lt _ hB
  have hrM : M ≤ r := by dsimp [r]; omega
  have hqM : M ≤ q := by dsimp [q]; nlinarith only [hd]
  have hrq : r ≤ q := by dsimp [r,q]; dsimp [B] at hs; nlinarith only [hs,hM,hd]
  have hqmod : q%b = 1 := by
    have hbq : b ∣ (m+M)*d := hbd.mul_left _
    dsimp [q]
    simp only [Nat.add_mod,Nat.mod_eq_zero_of_dvd hbq,zero_add,Nat.mod_eq_of_lt hb]
  have hsum : s+B*m = t-L := Nat.mod_add_div _ _
  have heq : d*r+(u-1)*q*(d+1)+1 = w := by
    have hLt' := Nat.sub_add_cancel hLt
    have hd1 := Nat.sub_add_cancel (by omega : 1 ≤ u)
    have ht' := congrArg (fun z => d*z) (show s+B*m+L = t by omega)
    dsimp [L] at ht'
    dsimp [r,q]
    dsimp [B] at ht'
    have hu' := congrArg (fun z => z) hd1
    nlinarith only [ht,ht',hu']
  exact ⟨r,q,hrM,hrq,hqM,hqmod,heq⟩

end Spectrum.PBD
