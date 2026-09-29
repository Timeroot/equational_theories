import equational_theories.Spectrum.PBD.Localization
import equational_theories.Spectrum.PBD.DesignTruncation

/-! The replication numbers of uniform PBDs form a PBD-closed set. -/
namespace Spectrum.PBD
open Classical PairDecomposition

namespace PairDecomposition.GroupDivisible
variable {K : Set ℕ} {I J : Type*} {A : I → Type*} {B : J → Type*}

noncomputable def relabel (D : GroupDivisible K A) (e : I ≃ J)
    (f : ∀ i, A i ≃ B (e i)) : GroupDivisible K B := by
  apply (D.transport (Equiv.sigmaCongr e f)).congr
  intro x y _
  change e.symm x.1 ≠ e.symm y.1 ↔ x.1 ≠ y.1
  exact e.symm.injective.ne_iff

noncomputable def ofCards [Finite I] [∀ i, Finite (A i)]
    (D : GroupDivisible K A) {r s : ℕ}
    (hI : Nat.card I = r) (hA : ∀ i, Nat.card (A i) = s) :
    GroupDivisible K (fun _ : Fin r => Fin s) := by
  let e : I ≃ Fin r := (Finite.card_eq.mp (by simpa using hI)).some
  let f (i : I) : A i ≃ Fin s := (Finite.card_eq.mp (by simpa using hA i)).some
  exact D.relabel e f

end PairDecomposition.GroupDivisible

/-- Replication number `r` corresponds to a uniform design on `(k-1)r+1` points. -/
def replications (k : ℕ) : Set ℕ := {r | (k-1)*r+1 ∈ designClosure {k}}

namespace Replication
variable {k r s : ℕ}

theorem of_groupDesign (hk : 2 ≤ k)
    (D : GroupDivisible ({k} : Set ℕ) (fun _ : Fin r => Fin (k-1))) :
    r ∈ replications k := by
  let E := D.adjoin 1 (by omega) (fun _ => singleBlock (by
    simp only [Nat.card_sum,Nat.card_fin,Set.mem_singleton_iff]
    omega))
  have hc : Nat.card (Fin 1 ⊕ (Σ _ : Fin r, Fin (k-1))) = (k-1)*r+1 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.mul_comm,Nat.add_comm]
  have h := mem_designClosure E
  rwa [hc] at h

theorem groupDesign (hk : 2 ≤ k) (hr : r ∈ replications k) :
    Nonempty (GroupDivisible ({k} : Set ℕ) (fun _ : Fin r => Fin (k-1))) := by
  obtain ⟨D⟩ := hr
  let o : Fin ((k-1)*r+1) := 0
  have hs (b : LocalGroups D o) : Nat.card (LocalGroup D o b) = k-1 := by
    rw [card_localGroup]
    have h := D.sizes _ b.val.property
    simpa only [Set.mem_singleton_iff] using congrArg (fun n => n-1) h
  have hc : Nat.card (LocalGroups D o) = r := by
    have ht := card_localPoints D o
    rw [Nat.card_fin,Nat.add_sub_cancel] at ht
    have ht' : Nat.card (Σ b : LocalGroups D o, LocalGroup D o b) =
        Nat.card (LocalGroups D o)*(k-1) := by
      letI := Fintype.ofFinite (LocalGroups D o)
      rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
      simp only [Fintype.card_eq_nat_card,hs,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rw [ht'] at ht
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < k-1) (ht.trans (Nat.mul_comm _ _))
  exact ⟨(D.localize o).ofCards hc hs⟩

/-- Hanani's closure theorem for replication numbers. -/
theorem closed (hk : 2 ≤ k) : DesignClosed (replications k) := by
  rintro n ⟨D⟩
  have ingredients (b : D.blocks) :
      Nonempty (GroupDivisible ({k} : Set ℕ) (fun _ : b.val => Fin (k-1))) := by
    obtain ⟨E⟩ := groupDesign hk (D.sizes _ b.property)
    let e : Fin (Nat.card b.val) ≃ b.val := (Finite.card_eq.mp (by simp)).some
    exact ⟨E.relabel e (fun _ => Equiv.refl _)⟩
  let E := (D.inflate (fun _ => Fin (k-1)) (fun b => (ingredients b).some)).congr
    (S := fun x y => x.1 ≠ y.1) (by intro x y _; simp)
  exact of_groupDesign hk E

/-- Multiply replication numbers using one fixed-order transversal design. -/
theorem mul (hk : 2 ≤ k) (hr : r ∈ replications k) (hs : s ∈ replications k)
    (T : HasTD k s) : r*s ∈ replications k := by
  obtain ⟨D⟩ := groupDesign hk hr
  obtain ⟨T⟩ := T
  have ingredients (b : D.blocks) :
      Nonempty (GroupDivisible ({k} : Set ℕ) (fun _ : b.val => Fin s)) := by
    have hc : Nat.card b.val = k := D.sizes _ b.property
    let e : b.val ≃ Fin k := (Finite.card_eq.mp (by simpa using hc)).some
    let T' := T.reindex e
    exact ⟨T'.completeGroups hc⟩
  let E := D.fundamental (fun _ => Fin s) (fun b => (ingredients b).some)
  have groups (i : Fin r) :
      Nonempty (Complete ({k} : Set ℕ) (Fin 1 ⊕ (Σ _ : Fin (k-1), Fin s))) := by
    obtain ⟨F⟩ := hs
    refine ⟨F.ofCard ?_⟩
    simp [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.add_comm]
  let F := E.adjoin 1 (by omega) (fun i => (groups i).some)
  have h := mem_designClosure F
  have hc : Nat.card (Fin 1 ⊕ (Σ _ : Fin r, Σ _ : Fin (k-1), Fin s)) = (k-1)*(r*s)+1 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_sigma]
    ring
  rwa [hc] at h

end Replication
end Spectrum.PBD
