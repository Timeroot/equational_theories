import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import equational_theories.FreeMagma

/-!
# Pair interpolation in a family closed under majority

A majority operation combines three partial witnesses: if each coordinate is
correct in at least two witnesses, their majority is correct there. Consequently,
on a finite domain, membership in a nonempty family closed under pointwise
majority can be checked on pairs of coordinates.

For term operations this applies when the source magma has a majority term.
The small-model search retains that term and a pair-compatible target table,
rather than storing the much larger binary term obtained by interpolation.
No universal definability arrow follows from one finite source having such a term.
-/

namespace Magma.MajorityInterpolation

variable {ι α : Type*} {C : Set (ι → α)} {m : α → α → α → α}

/-- Interpolate a finite set of coordinates using a majority operation. -/
theorem interpolate_finset
    (h₁ : ∀ x y, m x x y = x) (h₂ : ∀ x y, m x y x = x)
    (h₃ : ∀ x y, m y x x = x)
    (hne : C.Nonempty)
    (hclosed : ∀ f ∈ C, ∀ g ∈ C, ∀ h ∈ C, (fun i ↦ m (f i) (g i) (h i)) ∈ C)
    (f : ι → α) (hpair : ∀ i j, ∃ g ∈ C, g i = f i ∧ g j = f j)
    (s : Finset ι) : ∃ g ∈ C, ∀ i ∈ s, g i = f i := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.card ≤ 2
    · have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
      rcases hcases with h | h | h
      · obtain ⟨g, hg⟩ := hne
        exact ⟨g, hg, by simp [Finset.card_eq_zero.mp h]⟩
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
        obtain ⟨g, hg, ha, _⟩ := hpair a a
        exact ⟨g, hg, by simpa using ha⟩
      · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
        obtain ⟨g, hg, ha, hb⟩ := hpair a b
        exact ⟨g, hg, by simp_all⟩
    · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card_iff.mp (by omega : 2 < s.card)
      obtain ⟨u, hu, huf⟩ := ih (s.erase a) (Finset.erase_ssubset ha)
      obtain ⟨v, hv, hvf⟩ := ih (s.erase b) (Finset.erase_ssubset hb)
      obtain ⟨w, hw, hwf⟩ := ih (s.erase c) (Finset.erase_ssubset hc)
      refine ⟨fun i ↦ m (u i) (v i) (w i), hclosed u hu v hv w hw, ?_⟩
      intro i hi
      change m (u i) (v i) (w i) = f i
      by_cases hia : i = a
      · subst i
        rw [hvf a (by simp [ha, hab]), hwf a (by simp [ha, hac])]
        exact h₃ _ _
      · by_cases hib : i = b
        · subst i
          rw [huf b (by simp [hb, hab.symm]), hwf b (by simp [hb, hbc])]
          exact h₂ _ _
        · rw [huf i (by simp [hi, hia]), hvf i (by simp [hi, hib])]
          exact h₁ _ _

/-- Pairwise agreement suffices on a finite domain if the family is closed under majority. -/
theorem mem_of_pair_interpolation [Fintype ι]
    (h₁ : ∀ x y, m x x y = x) (h₂ : ∀ x y, m x y x = x)
    (h₃ : ∀ x y, m y x x = x)
    (hne : C.Nonempty)
    (hclosed : ∀ f ∈ C, ∀ g ∈ C, ∀ h ∈ C, (fun i ↦ m (f i) (g i) (h i)) ∈ C)
    (f : ι → α) (hpair : ∀ i j, ∃ g ∈ C, g i = f i ∧ g j = f j) : f ∈ C := by
  obtain ⟨g, hg, hgf⟩ := interpolate_finset h₁ h₂ h₃ hne hclosed f hpair Finset.univ
  have : g = f := funext fun i ↦ hgf i (Finset.mem_univ i)
  exact this ▸ hg

/-- A majority term turns pairwise interpolation into one binary term on a finite magma. -/
theorem binary_term_of_pair_interpolation {G : Type*} [Magma G] [Fintype G]
    (t : FreeMagma (Fin 3))
    (h₁ : ∀ x y : G, t.evalInMagma ![x, x, y] = x)
    (h₂ : ∀ x y : G, t.evalInMagma ![x, y, x] = x)
    (h₃ : ∀ x y : G, t.evalInMagma ![y, x, x] = x)
    (f : G → G → G)
    (hpair : ∀ a b c d, ∃ s : FreeMagma (Fin 2),
      s.evalInMagma ![a, b] = f a b ∧ s.evalInMagma ![c, d] = f c d) :
    ∃ s : FreeMagma (Fin 2), ∀ a b, s.evalInMagma ![a, b] = f a b := by
  let C : Set (G × G → G) := {g | ∃ s : FreeMagma (Fin 2),
    ∀ p, s.evalInMagma ![p.1, p.2] = g p}
  have hne : C.Nonempty := ⟨fun p ↦ p.1, .Leaf 0, by simp [FreeMagma.evalInMagma]⟩
  have hclosed : ∀ u ∈ C, ∀ v ∈ C, ∀ w ∈ C,
      (fun p ↦ t.evalInMagma ![u p, v p, w p]) ∈ C := by
    rintro u ⟨su, hu⟩ v ⟨sv, hv⟩ w ⟨sw, hw⟩
    refine ⟨t.evalInMagma ![su, sv, sw], fun p ↦ ?_⟩
    rw [FreeMagma.SubstEval]
    congr 1
    funext i
    fin_cases i <;> simp [hu, hv, hw]
  have hp : ∀ p q : G × G, ∃ g ∈ C,
      g p = f p.1 p.2 ∧ g q = f q.1 q.2 := by
    intro p q
    obtain ⟨s, hs, ht⟩ := hpair p.1 p.2 q.1 q.2
    exact ⟨fun p ↦ s.evalInMagma ![p.1, p.2], ⟨s, fun _ ↦ rfl⟩, hs, ht⟩
  obtain ⟨s, hs⟩ := mem_of_pair_interpolation
    (m := fun x y z ↦ t.evalInMagma ![x, y, z]) h₁ h₂ h₃ hne hclosed
    (fun p ↦ f p.1 p.2) hp
  exact ⟨s, fun a b ↦ hs (a, b)⟩

end Magma.MajorityInterpolation
