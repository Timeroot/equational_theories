import equational_theories.Definability.FORecoveryCompactness
import equational_theories.Definability.Structural

/-! The compactness bound also applies inside any family preserved by forward
parameter-free definitions. The same bound works for every family: the finite
cover is chosen before the carrier or its prescribed automorphisms. -/

open FirstOrder Law Law.MagmaLaw
namespace FORecoveryCompactness

abbrev RestrictedTables (A : NatMagmaLaw) (G : Type)
    (P : (G → G → G) → Prop) := {f : G → G → G // @satisfies _ G ⟨f⟩ A ∧ P f}

theorem Represents.definable {G : Type} {M N : Magma G} {q : GraphFormula}
    (h : Represents M N q) : @Set.Definable G ∅ MagmaLanguage M.FOStructure _ N.Graph := by
  letI := M.FOStructure
  rw [Set.empty_definable_iff]
  exact ⟨q, Set.ext fun v => (h v).symm⟩

theorem bounded_restricted_counts (A B : NatMagmaLaw) (h : B.StructuralFrom A) :
    ∃ K : ℕ, ∀ (G : Type) [Fintype G] [Nonempty G]
      (P : (G → G → G) → Prop),
      (∀ (M N : Magma G) (q : GraphFormula), Represents M N q → P M.op → P N.op) →
      Nat.card (RestrictedTables A G P) ≤ K * Nat.card (RestrictedTables B G P) := by
  classical
  obtain ⟨s, hs⟩ := finite_cover A B h
  refine ⟨s.card, ?_⟩
  intro G _ _ P hP
  have hc (f : RestrictedTables A G P) : ∃ p : s × RestrictedTables B G P,
      Represents (⟨p.2.val⟩ : Magma G) ⟨f.val⟩ p.1.val.2 := by
    obtain ⟨qr, hqr, hw⟩ := hs (⟨f.val⟩ : Magma G) f.property.1
    obtain ⟨N, hN, hf, hb⟩ := (realize_witness (⟨f.val⟩ : Magma G) B qr.1 qr.2).mp hw
    exact ⟨(⟨qr,hqr⟩, ⟨N.op,hN,hP _ _ _ hf f.property.2⟩), hb⟩
  choose p hp using hc
  have hi : Function.Injective p := by
    intro f g he
    have hg := hp g
    rw [← he] at hg
    have heq := represents_unique _ _ _ _ (hp f) hg
    apply Subtype.ext
    exact congrArg (fun t : Magma G => @Magma.op G t) heq
  have hle := Nat.card_le_card_of_injective p hi
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe] using hle

end FORecoveryCompactness
