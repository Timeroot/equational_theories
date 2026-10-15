import equational_theories.Definability.GenerationOrder
import equational_theories.Definability.FiniteFlavour
import Mathlib.Data.Finset.Card
import equational_theories.Definability.CollapsedUnaryProducts
open Law Law.MagmaLaw Magma.GenerationOrder
namespace RecoverySubmagmas

/-! Term recovery preserves idempotent points and submagmas. In particular,
the companion must generate at least as many points from a given seed as the
source does. These obstructions do not require a uniform recovering term. -/

theorem idempotent_of_termDefinable {G : Type} {M N : Magma G} (x : G)
    (h : @Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ N.FinArityOp)
    (hx : M.op x x = x) : N.op x x = x := by
  have hP : M.IsCloneInvariant (fun f => f x x = x) :=
    { fst := rfl, snd := rfl, comp := by
        intro f g hf hg
        dsimp only
        rw [hf, hg, hx] }
  exact hP.of_termDefinable h

/-- A magma has an idempotent term-structural companion exactly when it is
already idempotent. This holds separately for every carrier and every model. -/
theorem idempotent_companion_iff {G : Type} (M : Magma G) :
    Law3.TermStructuralOnMagma M ↔ @satisfies _ G M Law3 := by
  constructor
  · rintro ⟨N, hN, _, hr⟩
    apply (@Law3.models_iff G M).mpr
    intro x
    exact (idempotent_of_termDefinable x hr
      (((@Law3.models_iff G N).mp hN) x).symm).symm
  · exact TermStructural.refl M

theorem not_idempotent_recovery_all {G : Type} {A : NatMagmaLaw}
    (M : Magma G) (hA : @satisfies _ G M A) (x : G) (hx : M.op x x ≠ x) :
    ¬ Law3.TermStructuralFrom A := by
  intro h
  obtain ⟨N,hN,_,hr⟩ := h M hA
  apply hx
  exact idempotent_of_termDefinable x hr (((@Law3.models_iff G N).mp hN) x).symm

theorem not_idempotent_recovery {G : Type} [Finite G] {A : NatMagmaLaw}
    (M : Magma G) (hA : @satisfies _ G M A) (x : G) (hx : M.op x x ≠ x) :
    ¬ Law3.TermStructuralFromFin A := by
  intro h
  obtain ⟨N,hN,_,hr⟩ := h M hA
  apply hx
  exact idempotent_of_termDefinable x hr (((@Law3.models_iff G N).mp hN) x).symm

theorem cardinal_le_of_recovery {G : Type} [Fintype G] [DecidableEq G]
    {M N : Magma G} {x : G}
    (hg : ∀ z, Generated M.op {x} z)
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ M.FinArityOp)
    (S : Finset G) (hx : x ∈ S) (hc : Closed N.op (S : Set G)) :
    Fintype.card G ≤ S.card := by
  have hsub : Finset.univ ⊆ S := by
    intro z _
    apply (generated_of_recovery hr (hg z)) (S : Set G) _ hc
    simpa using hx
  simpa using Finset.card_le_card hsub

theorem three_closed {G : Type} [DecidableEq G] (M : Magma G) (x : G)
    (ht : CollapsedUnaryProducts.Table M x) :
    Closed M.op ({x, M.op x x, M.op (M.op x x) (M.op x x)} : Finset G) := by
  intro a ha b hb
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  unfold CollapsedUnaryProducts.Table at ht
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> grind

theorem card_le_three_of_recovery {G : Type} [Fintype G] [DecidableEq G]
    {M N : Magma G} {x : G}
    (hg : ∀ z, Generated M.op {x} z)
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ M.FinArityOp)
    (ht : CollapsedUnaryProducts.Table N x) : Fintype.card G ≤ 3 := by
  exact (cardinal_le_of_recovery hg hr _ (by simp) (three_closed N x ht)).trans
    Finset.card_le_three

theorem cardinal_le_of_closed_range {G : Type} [Fintype G] [DecidableEq G]
    {M N : Magma G} {x : G} {k : Nat}
    (hg : ∀ z, Generated M.op {x} z)
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ M.FinArityOp)
    (v : Fin k → G) (hx : ∃ i, v i = x) (hc : Closed N.op (Set.range v)) :
    Fintype.card G ≤ k := by
  have hmem : x ∈ Finset.univ.image v := by
    rcases hx with ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hclosed : Closed N.op (↑(Finset.univ.image v) : Set G) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hc
  exact (cardinal_le_of_recovery hg hr _ hmem hclosed).trans
    (by simpa using Finset.card_image_le (s := Finset.univ) (f := v))

end RecoverySubmagmas
