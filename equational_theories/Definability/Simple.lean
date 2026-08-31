import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Equations.All
import equational_theories.Duals.Basic
import equational_theories.Preorder
import equational_theories.MagmaOp

/-!
Proofs of some simple cases of definability.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

@[simp]
theorem FreeMagma.toTerm_realize {α M} (t : FreeMagma α)
    [inst : Magma M] (v : α → M) :
    @Term.realize _ _ inst.FOStructure _ v t.toTerm = t.evalInMagma v := by
  induction t with
  | Leaf a => rw [evalInMagma]; rfl
  | Fork m1 m2 ih1 ih2 =>
    rw [FreeMagma.toTerm]
    simp [Magma.FinArityOp, evalInMagma, ih1, ih2]

/-- Every law is TermStructural from its dual. -/
theorem TermStructural_dual (L : NatMagmaLaw) : L.TermStructuralFrom L.dual := by
  intro G M hGL
  refine ⟨⟨fun x y ↦ M.op y x⟩, ?_, ?_⟩
  · rw [← law_dual_dual L]
    exact @satisfies_dual_dual _ _ ⟨_⟩ _ hGL
  · constructor <;> exact ⟨Functions.apply₂ (Sum.inl ()) (Term.var 1) (Term.var 0), rfl⟩

/-- A law is TermStructural from anything its dual is equivalent to, and conversely: the opposite
magma reads either direction. -/
theorem TermStructural_isDual {L L' : NatMagmaLaw} (h : L.IsDual L') :
    L'.TermStructuralFrom L := by
  have i : L.implies L'.dual := by
    intro G _ hG
    exact (h G).mp hG
  intro G M hGL
  exact TermStructural.trans (termStructural_of_implies i) (TermStructural_dual L') M hGL

/-- **Structurality transports across duality on both sides.**  A device that works on the hub's
side of the implication graph settles the dual cell of the board as well, and this is the only
thing the emitted dual rows need: `IsDual` on the source, `IsDual` on the target, and the proof
in between. -/
theorem Structural_isDual {L₁ L₂ L₁' L₂' : NatMagmaLaw}
    (h₁ : L₁.IsDual L₁') (h₂ : L₂.IsDual L₂') (h : L₂'.StructuralFrom L₁') :
    L₂.StructuralFrom L₁ := by
  have s₁ : L₁'.StructuralFrom L₁ :=
    structural_of_termStructural (TermStructural_isDual h₁)
  have s₂ : L₂.StructuralFrom L₂' :=
    structural_of_termStructural (TermStructural_isDual h₂.symm)
  intro G M hGL
  exact Structural.trans (Structural.trans s₁ h) s₂ M hGL

/-- The identity law x=x is TermDefinable from anything. This is a direct consequence of the
fact that anything implies Eq1. -/
theorem Equation1_termDefinableFrom_all (L : NatMagmaLaw) : Law1.TermDefinableFrom L := by
  refine termDefinable_of_termStructural (termStructural_of_implies fun _ ↦ ?_)
  simp [Law1.models_iff, Equation1]

/-- Anything is TermDefinable from Eq2. This is a direct consequence of the fact that Eq2 implies
anything. -/
theorem all_termDefinableFrom_Equation2 (L : NatMagmaLaw) : L.TermDefinableFrom Law2 := by
  refine termDefinable_of_termStructural (termStructural_of_implies ?_)
  simpa [implies] using Equation2_implies L

/-- The left projection law is TermDefinable from anything. -/
theorem Equation4_termDefinableFrom_all (L : NatMagmaLaw) : Law4.TermDefinableFrom L := by
  intro G M hGL
  refine ⟨⟨fun x _ ↦ x⟩, ?_, ?_⟩
  · rw [@Law4.models_iff]
    exact fun _ _ => rfl
  · exact ⟨Term.var 0, rfl⟩

/-- The right projection law is TermDefinable from anything. -/
theorem Equation5_termDefinableFrom_all (L : NatMagmaLaw) : Law5.TermDefinableFrom L :=
  TermDefinable.trans (Equation4_termDefinableFrom_all L)
  <| termDefinable_of_termStructural (TermStructural_dual Law5)

/-- The associative law is TermDefinable from anything. -/
theorem Equation4512_termDefinableFrom_all (L : NatMagmaLaw) : Law4512.TermDefinableFrom L :=
  have : Law4.implies Law4512 := by
    intro _ _ h
    simp only [Law4.models_iff, Law4512.models_iff, Equation4512] at h ⊢
    simp [← h]
  TermDefinable.trans (Equation4_termDefinableFrom_all L)
  <| termDefinable_of_termStructural (termStructural_of_implies (this))
