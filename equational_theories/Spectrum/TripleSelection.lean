import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Selecting invariant subsets of a permutation whose cycles have length three. -/
namespace Spectrum.TripleSelection
open Finset
variable {A : Type*} [DecidableEq A] (g : A → A)
  (hg : ∀ x, g (g (g x)) = x)

def orbit (a : A) : Finset A := {a, g a, g (g a)}

include hg

theorem orbit_mem (a x : A) : g x ∈ orbit g a ↔ x ∈ orbit g a := by
  simp only [orbit, mem_insert, mem_singleton]
  constructor
  · rintro (h | h | h)
    · right; right
      simpa only [hg] using congrArg (fun t => g (g t)) h
    · left
      simpa only [hg] using congrArg (fun t => g (g t)) h
    · right; left
      simpa only [hg] using congrArg (fun t => g (g t)) h
  · rintro (rfl | rfl | rfl) <;> simp [hg]

theorem orbit_card {a : A} (ha : g a ≠ a) : (orbit g a).card = 3 := by
  have h2 : g (g a) ≠ a := by
    intro h
    have := congrArg g h
    rw [hg] at this
    exact ha this.symm
  have h3 : g (g a) ≠ g a := by
    intro h
    have := congrArg (fun t => g (g t)) h
    simp only [hg] at this
    exact ha this
  simp [orbit, Ne.symm ha, Ne.symm h2, Ne.symm h3]

theorem select (k : ℕ) (s : Finset A)
    (hc : ∀ x ∈ s, g x ∈ s) (hf : ∀ x ∈ s, g x ≠ x)
    (hk : 3 * k ≤ s.card) :
    ∃ t ⊆ s, t.card = 3 * k ∧ ∀ x ∈ t, g x ∈ t := by
  induction k generalizing s with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0 < s.card)
    let o := orbit g a
    have ho : o.card = 3 := orbit_card g hg (hf a ha)
    have hos : o ⊆ s := by
      intro x hx
      simp only [o, orbit, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hc a ha
      · exact hc _ (hc a ha)
    have hclosed : ∀ x ∈ s \ o, g x ∈ s \ o := by
      intro x hx
      obtain ⟨hs,hn⟩ := mem_sdiff.mp hx
      exact mem_sdiff.mpr ⟨hc x hs, fun he => hn ((orbit_mem g hg a x).mp he)⟩
    have hs : (s \ o).card = s.card - 3 := by rw [card_sdiff_of_subset hos, ho]
    obtain ⟨t,ht,hcard,hct⟩ := ih (s \ o) hclosed
      (fun x hx => hf x (mem_sdiff.mp hx).1) (by omega)
    refine ⟨o ∪ t, union_subset hos (ht.trans sdiff_subset), ?_, ?_⟩
    · have hd : Disjoint o t := disjoint_left.mpr fun x hx hxt => (mem_sdiff.mp (ht hxt)).2 hx
      rw [card_union_of_disjoint hd, ho, hcard]
      omega
    · intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact mem_union_left _ ((orbit_mem g hg a x).mpr hx)
      · exact mem_union_right _ (hct x hx)

end Spectrum.TripleSelection
