import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! Elementary arithmetic of eventual periods of sets of natural numbers. -/
namespace Spectrum.PBD
open Classical

def EventuallyPeriodic (C : Set ℕ) (d : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → (n+d ∈ C ↔ n ∈ C)

/-- Only positive seeds are used: the empty PBD is not a residue witness. -/
def CompleteFibres (C : Set ℕ) (d : ℕ) : Prop :=
  ∀ u, 0 < u → u ∈ C → ∃ N, ∀ n, N ≤ n → n ≡ u [MOD d] → n ∈ C

namespace EventuallyPeriodic
variable {C : Set ℕ} {a b d : ℕ}

theorem multiples (h : EventuallyPeriodic C d) :
    ∃ N, ∀ n, N ≤ n → ∀ t, (n+t*d ∈ C ↔ n ∈ C) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨N,?_⟩
  intro n hn t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul,← Nat.add_assoc]
    exact (hN (n+t*d) (by omega)).trans ih

theorem mul (h : EventuallyPeriodic C d) (t : ℕ) : EventuallyPeriodic C (t*d) := by
  obtain ⟨N,hN⟩ := h.multiples
  exact ⟨N,fun n hn => hN n hn t⟩

theorem sub (ha : EventuallyPeriodic C a) (hb : EventuallyPeriodic C b) (hba : b ≤ a) :
    EventuallyPeriodic C (a-b) := by
  obtain ⟨A,hA⟩ := ha
  obtain ⟨B,hB⟩ := hb
  refine ⟨max A B,?_⟩
  intro n hn
  have hb' := hB (n+(a-b)) (by omega)
  have ha' := hA n (by omega)
  have heq : n+(a-b)+b = n+a := by omega
  rw [heq] at hb'
  exact hb'.symm.trans ha'

theorem mod (ha : EventuallyPeriodic C a) (hb : EventuallyPeriodic C b) :
    EventuallyPeriodic C (a%b) := by
  have h := ha.sub (hb.mul (a/b)) (Nat.div_mul_le_self a b)
  simpa only [Nat.mod_eq_sub_div_mul] using h

theorem gcd (ha : EventuallyPeriodic C a) (hb : EventuallyPeriodic C b) :
    EventuallyPeriodic C (Nat.gcd a b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha0 : a = 0
    · simpa [ha0] using hb
    rw [Nat.gcd_rec]
    exact ih (b%a) (Nat.mod_lt b (by omega)) (hb.mod ha) ha

theorem same_residue (h : EventuallyPeriodic C d) :
    ∃ N, ∀ n m, N ≤ n → N ≤ m → n ≡ m [MOD d] → (n ∈ C ↔ m ∈ C) := by
  obtain ⟨N,hN⟩ := h.multiples
  refine ⟨N,?_⟩
  intro n m hn hm hmod
  rcases le_total n m with hle | hle
  · obtain ⟨t,ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
    rw [ht,Nat.mul_comm d t]
    exact (hN n hn t).symm
  · obtain ⟨t,ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    rw [ht,Nat.mul_comm d t]
    exact hN m hm t
end EventuallyPeriodic

theorem CompleteFibres.eventuallyPeriodic {C : Set ℕ} {d : ℕ}
    (h : CompleteFibres C d) (hd : 0 < d) : EventuallyPeriodic C d := by
  have tails : ∀ r : Fin d, ∃ A, ∀ n, A ≤ n → n % d = r.val →
      (∃ u, 0 < u ∧ u ∈ C ∧ u % d = r.val) → n ∈ C := by
    intro r
    by_cases hex : ∃ u, 0 < u ∧ u ∈ C ∧ u % d = r.val
    · obtain ⟨u,hu,huC,hur⟩ := hex
      obtain ⟨A,hA⟩ := h u hu huC
      exact ⟨A,fun n hn hnr _ => hA n hn (hnr.trans hur.symm)⟩
    · exact ⟨0,fun _ _ _ he => (hex he).elim⟩
  choose A hA using tails
  let N := Finset.univ.sup A + 1
  refine ⟨N,?_⟩
  intro n hn
  let r : Fin d := ⟨n%d,Nat.mod_lt n hd⟩
  have hAn : A r ≤ n := by
    have h := Finset.le_sup (f := A) (Finset.mem_univ r)
    dsimp [N] at hn
    omega
  have hnpos : 0 < n := by dsimp [N] at hn; omega
  have hmod : (n+d)%d = r.val := by simp [r]
  constructor
  · intro hnd
    exact hA r n hAn rfl ⟨n+d,by omega,hnd,hmod⟩
  · intro hnc
    exact hA r (n+d) (by omega) hmod ⟨n,hnpos,hnc,rfl⟩

end Spectrum.PBD
