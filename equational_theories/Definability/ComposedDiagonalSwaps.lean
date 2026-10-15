import equational_theories.Definability.DiagonalOutputSwap

/-! Two reversible swaps can enforce a law even when the intermediate magma
satisfies no useful catalogue law. Their definable inverses compose in reverse order. -/
open Law Law.MagmaLaw DiagonalOutputSwap
namespace Law.MagmaLaw

theorem structuralFrom_twoDiagonalSwaps {A B : NatMagmaLaw}
    (i j k l : Fin 6) (o : Bool)
    (target : ∀ {G : Type} (M : Magma G), satisfies G A →
      @satisfies _ G ((forward k l false).magma ((forward i j o).magma M)) B) :
    B.StructuralFrom A := by
  intro G M hM
  let N := (forward i j o).magma M
  refine ⟨(forward k l false).magma N, target M hM, ?_, ?_⟩
  · exact Definable.trans_aux ((forward i j o).definable_graph M)
      ((forward k l false).definable_graph N)
  · have r₂ := (backward k l false).definable_graph ((forward k l false).magma N)
    have r₁ := (backward i j o).definable_graph N
    rw [recover] at r₂
    dsimp only [N] at r₁
    rw [recover] at r₁
    exact Definable.trans_aux r₂ r₁
end Law.MagmaLaw

/-- info: 'Law.MagmaLaw.structuralFrom_twoDiagonalSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.structuralFrom_twoDiagonalSwaps

namespace Law.MagmaLaw
theorem structuralFrom_threeDiagonalSwaps {A B : NatMagmaLaw}
    (i j k l u v : Fin 6) (o : Bool)
    (target : ∀ {G : Type} (M : Magma G), satisfies G A →
      @satisfies _ G ((forward u v false).magma
        ((forward k l false).magma ((forward i j o).magma M))) B) :
    B.StructuralFrom A := by
  intro G M hM
  let N₁ := (forward i j o).magma M
  let N₂ := (forward k l false).magma N₁
  refine ⟨(forward u v false).magma N₂, target M hM, ?_, ?_⟩
  · exact Definable.trans_aux
      (Definable.trans_aux ((forward i j o).definable_graph M)
        ((forward k l false).definable_graph N₁))
      ((forward u v false).definable_graph N₂)
  · have r₃ := (backward u v false).definable_graph ((forward u v false).magma N₂)
    have r₂ := (backward k l false).definable_graph N₂
    have r₁ := (backward i j o).definable_graph N₁
    rw [recover] at r₃
    dsimp only [N₂] at r₂
    rw [recover] at r₂
    dsimp only [N₁] at r₁
    rw [recover] at r₁
    exact Definable.trans_aux r₃ (Definable.trans_aux r₂ r₁)
end Law.MagmaLaw

/-- info: 'Law.MagmaLaw.structuralFrom_threeDiagonalSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.structuralFrom_threeDiagonalSwaps
