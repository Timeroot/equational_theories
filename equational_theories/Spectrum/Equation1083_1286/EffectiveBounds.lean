import equational_theories.Spectrum.Equation1083_1286.DesignWitnesses

/-! A quantitative reduction for E1083 and E1286. The finite construction
certificate and the explicit transversal-design gap must be checked separately;
this theorem does not assert either numerical hypothesis. -/
namespace Spectrum.E1083E1286.EffectiveBounds
open Law Law.MagmaLaw

private theorem model_of_hasModel {which : Bool} {n : ℕ}
    (h : (law which).HasModel n) : Model which (Fin n) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m.op, ?_, by simp⟩
  cases which
  · exact fun x y => ((@Law1083.models_iff (Fin n) m).mp hm x y).symm
  · exact fun x y => ((@Law1286.models_iff (Fin n) m).mp hm x y).symm

/-- A finite interval and a uniform TD gap suffice for an infinite tail.
The hole stays below `C + 1008*G`, while the full groups use smaller orders
to which strong induction applies. -/
theorem tail {which : Bool} {C G : ℕ} (hC : 0 < C) (hG : 0 < G)
    (gap : ∀ a, 0 < a → ∃ q, a ≤ q ∧ q < a+G ∧ PBD.HasTD 1009 q)
    (base : ∀ n, C ≤ n → n ≤ 1009*(C+1008*G) → (law which).HasModel n) :
    ∀ n, C ≤ n → (law which).HasModel n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hb : n ≤ 1009*(C+1008*G)
    · exact base n hn hb
    let a := (n-(C+1008*G))/1008+1
    obtain ⟨q, hqa, hqg, hD⟩ := gap a (by dsimp [a]; omega)
    let r := n-1008*q
    have bounds : C ≤ q ∧ q < n ∧ C ≤ r ∧ r < C+1008*G ∧ r ≤ q ∧
        1008*q+r=n := by
      dsimp [a] at hqa hqg
      dsimp [r]
      omega
    obtain ⟨hqC,hqn,hrC,hrB,hrq,he⟩ := bounds
    rw [← he]
    exact hasTD_models hD hrq (model_of_hasModel (ih q hqn hqC))
      (model_of_hasModel (base r hrC (by omega))) idem1008 idem1009

end Spectrum.E1083E1286.EffectiveBounds

/-- info: 'Spectrum.E1083E1286.EffectiveBounds.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.E1083E1286.EffectiveBounds.tail
