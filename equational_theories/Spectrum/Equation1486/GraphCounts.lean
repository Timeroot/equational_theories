import equational_theories.Spectrum.Equation1486.Graph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Cardinality ranges of the split-edge E1486 construction. -/

namespace Spectrum.E1486

open Finset
attribute [local instance] Classical.propDecidable
noncomputable section

private def pairedGraph (k : ℕ) : SimpleGraph (Fin k × Bool) where
  Adj a b := a.1 ≠ b.1
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

private def distinctPairEquiv (k : ℕ) :
    {p : Fin k × Fin k // p.1 = p.2} ≃ Fin k where
  toFun p := p.val.1
  invFun a := ⟨(a,a), rfl⟩
  left_inv := by rintro ⟨⟨a,b⟩, h⟩; cases h; rfl
  right_inv _ := rfl

private theorem distinctPair_card (k : ℕ) :
    Fintype.card {p : Fin k × Fin k // p.1 ≠ p.2} = k * (k - 1) := by
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_congr (distinctPairEquiv k)]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

private def pairedDartEquiv (k : ℕ) :
    {p : (Fin k × Bool) × (Fin k × Bool) // (pairedGraph k).Adj p.1 p.2} ≃
      {p : Fin k × Fin k // p.1 ≠ p.2} × (Bool × Bool) where
  toFun p := (⟨(p.val.1.1, p.val.2.1), p.prop⟩, p.val.1.2, p.val.2.2)
  invFun p := ⟨((p.1.val.1,p.2.1),(p.1.val.2,p.2.2)), p.1.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pairedGraph_card (k : ℕ) :
    Fintype.card {p : (Fin k × Bool) × (Fin k × Bool) //
      (pairedGraph k).Adj p.1 p.2} = 4 * k * (k - 1) := by
  classical
  rw [Fintype.card_congr (pairedDartEquiv k)]
  simp only [Fintype.card_prod, Fintype.card_bool, distinctPair_card]
  ring

private def oddGraph (k : ℕ) (a₀ : Fin k × Bool) :
    SimpleGraph (Option (Fin k × Bool)) where
  Adj
    | some a, some b => a.1 ≠ b.1
    | none, some b => b ≠ a₀
    | some a, none => a ≠ a₀
    | none, none => False
  symm := by intro a b; cases a <;> cases b <;> simp_all [ne_comm]
  loopless := ⟨by intro a; cases a <;> simp_all⟩

private def oddDartEquiv (k : ℕ) (a₀ : Fin k × Bool) :
    {p : Option (Fin k × Bool) × Option (Fin k × Bool) //
      (oddGraph k a₀).Adj p.1 p.2} ≃
    {p : (Fin k × Bool) × (Fin k × Bool) // (pairedGraph k).Adj p.1 p.2} ⊕
      (Bool × {a : Fin k × Bool // a ≠ a₀}) where
  toFun
    | ⟨(some a,some b), h⟩ => .inl ⟨(a,b),h⟩
    | ⟨(none,some b), h⟩ => .inr (false,⟨b,h⟩)
    | ⟨(some a,none), h⟩ => .inr (true,⟨a,h⟩)
    | ⟨(none,none), h⟩ => False.elim h
  invFun
    | .inl p => ⟨(some p.val.1,some p.val.2),p.prop⟩
    | .inr (false,a) => ⟨(none,some a.val),a.prop⟩
    | .inr (true,a) => ⟨(some a.val,none),a.prop⟩
  left_inv := by
    rintro ⟨⟨a,b⟩, h⟩
    cases a <;> cases b <;> first | rfl | exact False.elim h
  right_inv := by
    rintro (p | ⟨b,a⟩)
    · rfl
    · cases b <;> rfl

private theorem oddGraph_card (k : ℕ) (a₀ : Fin k × Bool) :
    Fintype.card {p : Option (Fin k × Bool) × Option (Fin k × Bool) //
      (oddGraph k a₀).Adj p.1 p.2} =
        4 * k * (k - 1) + 2 * (2 * k - 1) := by
  classical
  rw [Fintype.card_congr (oddDartEquiv k a₀)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    pairedGraph_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Fintype.card_fin]
  congr 2
  omega

/-- Choosing any prescribed number of the edges preserves the hypothesis
that every vertex has a distinct nonneighbor. -/
theorem graph_interval {A : Type} [Fintype A] [LinearOrder A]
    (G : SimpleGraph A) (hG : ∀ a, ∃ b, b ≠ a ∧ ¬ G.Adj b a)
    (m : ℕ) (hm : m ≤ G.edgeFinset.card) :
    Law1486.HasModel (Fintype.card A ^ 2 + 2 * m) := by
  classical
  obtain ⟨t, ht, htm⟩ := Finset.exists_subset_card_eq hm
  let H := SimpleGraph.fromEdgeSet (t : Set (Sym2 A))
  have hle : H ≤ G := by
    intro a b hab
    exact SimpleGraph.mem_edgeFinset.mp (ht hab.1)
  have hedge : H.edgeSet = (t : Set (Sym2 A)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun h => h.1
    · intro he
      exact ⟨he, fun hd => G.not_isDiag_of_mem_edgeFinset (ht he) hd⟩
  have hcard : Fintype.card {p : A × A // H.Adj p.1 p.2} = 2 * m := by
    rw [Fintype.card_subtype, ← H.two_mul_card_edgeFinset]
    simp [SimpleGraph.edgeFinset, hedge, htm]
  choose d hd hdE using hG
  have hh := hasModel H.Adj (fun a => H.loopless.irrefl a) (fun _ _ h => H.symm h) d hd
    (fun a h => hdE a (hle h))
  simpa only [hcard] using hh

/-- The complement of a perfect matching supplies the full even-vertex
range, including every intermediate number of edges. -/
theorem even_graph_interval (k m : ℕ) (hm : m ≤ 2 * k * (k - 1)) :
    Law1486.HasModel ((2 * k) ^ 2 + 2 * m) := by
  classical
  letI : LinearOrder (Fin k × Bool) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hc : 2 * (pairedGraph k).edgeFinset.card = 4 * k * (k - 1) := by
    rw [SimpleGraph.two_mul_card_edgeFinset, ← Fintype.card_subtype]
    exact pairedGraph_card k
  have hG : ∀ a : Fin k × Bool, ∃ b, b ≠ a ∧ ¬ (pairedGraph k).Adj b a := by
    rintro ⟨a,b⟩
    refine ⟨(a,!b), ?_, ?_⟩
    · cases b <;> simp
    · simp [pairedGraph]
  have h := graph_interval (pairedGraph k) hG m (by nlinarith)
  simpa [Fintype.card_prod, Nat.mul_comm] using h

/-- On an odd number of vertices, add one vertex to the preceding graph,
joining it to all old vertices except one. -/
theorem odd_graph_interval (k m : ℕ) (hk : 1 ≤ k)
    (hm : m ≤ 2 * k * (k - 1) + (2 * k - 1)) :
    Law1486.HasModel ((2 * k + 1) ^ 2 + 2 * m) := by
  classical
  letI : LinearOrder (Option (Fin k × Bool)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let a₀ : Fin k × Bool := (⟨0,by omega⟩,false)
  have hc : 2 * (oddGraph k a₀).edgeFinset.card =
      4 * k * (k - 1) + 2 * (2 * k - 1) := by
    rw [SimpleGraph.two_mul_card_edgeFinset, ← Fintype.card_subtype]
    exact oddGraph_card k a₀
  have hG : ∀ a : Option (Fin k × Bool),
      ∃ b, b ≠ a ∧ ¬ (oddGraph k a₀).Adj b a := by
    intro a
    cases a with
    | none => exact ⟨some a₀, by simp, by simp [oddGraph]⟩
    | some a =>
      refine ⟨some (a.1,!a.2), ?_, ?_⟩
      · cases a with | mk a b => cases b <;> simp
      · simp [oddGraph]
  have h := graph_interval (oddGraph k a₀) hG m (by nlinarith)
  simpa [Fintype.card_prod, Nat.mul_comm] using h

private theorem even_intervals_cover (t : ℕ) (ht : 32 ≤ t) :
    ∃ k m : ℕ, 4 ≤ k ∧ t = 2 * k ^ 2 + m ∧ m ≤ 2 * k * (k - 1) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases hb : t = 32
    · subst t
      exact ⟨4,0,by norm_num,by norm_num,by norm_num⟩
    have hs : t - 1 + 1 = t := by omega
    obtain ⟨k,m,hk,he,hm⟩ := ih (t - 1) (by omega) (by omega)
    by_cases hfit : m + 1 ≤ 2 * k * (k - 1)
    · exact ⟨k,m+1,hk,by omega,hfit⟩
    have hkm : k - 1 + 1 = k := by omega
    have hmul : 4 * k ≤ k * k := by nlinarith [Nat.mul_le_mul_left k hk]
    have hmlo : 4 * k + 1 ≤ m := by nlinarith
    have hms : m - (4 * k + 1) + (4 * k + 1) = m := by omega
    refine ⟨k+1,m-(4*k+1),by omega,?_,?_⟩
    · nlinarith
    · simp only [Nat.add_sub_cancel]
      nlinarith

private theorem odd_intervals_cover (t : ℕ) (ht : 24 ≤ t) :
    ∃ k m : ℕ, 3 ≤ k ∧ t = 2 * k ^ 2 + 2 * k + m ∧
      m ≤ 2 * k * (k - 1) + (2 * k - 1) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases hb : t = 24
    · subst t
      exact ⟨3,0,by norm_num,by norm_num,by norm_num⟩
    have hs : t - 1 + 1 = t := by omega
    obtain ⟨k,m,hk,he,hm⟩ := ih (t - 1) (by omega) (by omega)
    by_cases hfit : m + 1 ≤ 2 * k * (k - 1) + (2 * k - 1)
    · exact ⟨k,m+1,hk,by omega,hfit⟩
    have hkm : k - 1 + 1 = k := by omega
    have h2km : 2 * k - 1 + 1 = 2 * k := by omega
    have hmul : 3 * k ≤ k * k := by nlinarith [Nat.mul_le_mul_left k hk]
    have hmlo : 4 * k + 3 ≤ m := by nlinarith
    have hms : m - (4 * k + 3) + (4 * k + 3) = m := by omega
    refine ⟨k+1,m-(4*k+3),by omega,?_,?_⟩
    · nlinarith
    · simp only [Nat.add_sub_cancel]
      have h2k : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [h2k]
      nlinarith

/-- Every even order at least 64 occurs in the E1486 spectrum. -/
theorem even_atLeast64 (N : ℕ) (hN : 64 ≤ N) (hp : N % 2 = 0) :
    Law1486.HasModel N := by
  obtain ⟨k,m,hk,he,hm⟩ := even_intervals_cover (N / 2) (by omega)
  have hN' : N = 2 * (N / 2) := by omega
  have hcard : (2 * k) ^ 2 + 2 * m = N := by nlinarith
  rw [← hcard]
  exact even_graph_interval k m hm

/-- Every odd order at least 49 occurs in the E1486 spectrum. -/
theorem odd_atLeast49 (N : ℕ) (hN : 49 ≤ N) (hp : N % 2 = 1) :
    Law1486.HasModel N := by
  obtain ⟨k,m,hk,he,hm⟩ := odd_intervals_cover (N / 2) (by omega)
  have hN' : N = 2 * (N / 2) + 1 := by omega
  have hcard : (2 * k + 1) ^ 2 + 2 * m = N := by nlinarith
  rw [← hcard]
  exact odd_graph_interval k m (by omega) hm

/-- The graph construction proves an explicit cofinite E1486 spectrum. -/
theorem graph_atLeast63 (N : ℕ) (hN : 63 ≤ N) : Law1486.HasModel N := by
  by_cases hp : N % 2 = 0
  · exact even_atLeast64 N (by omega) hp
  · exact odd_atLeast49 N (by omega) (by omega)

/-- info: 'Spectrum.E1486.graph_atLeast63' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_atLeast63

end
end Spectrum.E1486
