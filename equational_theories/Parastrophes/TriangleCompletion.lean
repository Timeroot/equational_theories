import equational_theories.Mathlib.Order.Greedy
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Insert

/-! Completing disjoint oriented triangles, while controlling selected points.
The only extension input is the ability to find two fresh partners for a point. -/
namespace Parastrophes.TriangleCompletion

noncomputable section
variable {G : Type} [Group G]

structure Partial (allowed : G → G → Prop) where
  carrier : Finset G
  turn : G → G
  closed : ∀ x ∈ carrier, turn x ∈ carrier
  cube : ∀ x ∈ carrier, turn (turn (turn x)) = x
  triangle : ∀ x ∈ carrier, x * turn (turn x) * turn x = 1
  control : ∀ x ∈ carrier, allowed x (turn (turn x))

namespace Partial
variable {allowed : G → G → Prop}

instance : Preorder (Partial allowed) where
  le p q := p.carrier ⊆ q.carrier ∧ ∀ x ∈ p.carrier, q.turn x = p.turn x
  le_refl _ := ⟨fun _ h => h, fun _ _ => rfl⟩
  le_trans p q r hp hq := ⟨fun _ h => hq.1 (hp.1 h), fun x hx =>
    (hq.2 x (hp.1 hx)).trans (hp.2 x hx)⟩

def empty : Partial allowed where
  carrier := ∅
  turn := id
  closed := by simp
  cube := by simp
  triangle := by simp
  control := by simp

/-- Insert a whole cycle into unused points. -/
def insert (p : Partial allowed) (a b c : G)
    (ha : a ∉ p.carrier) (hb : b ∉ p.carrier) (hc : c ∉ p.carrier)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : a * c * b = 1)
    (hA : allowed a c) (hB : allowed b a) (hC : allowed c b) : Partial allowed := by
  classical
  let s := fun x => if x = a then b else if x = b then c else if x = c then a else p.turn x
  have sa : s a = b := by simp [s]
  have sb : s b = c := by simp [s, hab.symm]
  have sc : s c = a := by simp [s, hac.symm, hbc.symm]
  have sold (x : G) (hx : x ∈ p.carrier) : s x = p.turn x := by
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    have hxb : x ≠ b := fun h => hb (h ▸ hx)
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    simp [s, hxa, hxb, hxc]
  have htB : b * a * c = 1 := by
    have := congrArg (fun x => b * x * b⁻¹) ht
    simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using this
  have htC : c * b * a = 1 := by
    have := congrArg (fun x => a⁻¹ * x * a) ht
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using this
  refine ⟨{a,b,c} ∪ p.carrier, s, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with ((rfl | rfl | rfl) | hx)
    · simp [sa]
    · simp [sb]
    · simp [sc]
    · exact Or.inr (sold x hx ▸ p.closed x hx)
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with ((rfl | rfl | rfl) | hx)
    · rw [sa, sb, sc]
    · rw [sb, sc, sa]
    · rw [sc, sa, sb]
    · rw [sold x hx, sold _ (p.closed x hx), sold _ (p.closed _ (p.closed x hx))]
      exact p.cube x hx
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with ((rfl | rfl | rfl) | hx)
    · simpa [sa, sb] using ht
    · simpa [sb, sc] using htB
    · simpa [sc, sa] using htC
    · rw [sold x hx, sold _ (p.closed x hx)]
      exact p.triangle x hx
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with ((rfl | rfl | rfl) | hx)
    · simpa [sa, sb] using hA
    · simpa [sb, sc] using hB
    · simpa [sc, sa] using hC
    · rw [sold x hx, sold _ (p.closed x hx)]
      exact p.control x hx

theorem le_insert (p : Partial allowed) (a b c : G) ha hb hc hab hac hbc ht hA hB hC :
    p ≤ p.insert a b c ha hb hc hab hac hbc ht hA hB hC := by
  classical
  constructor
  · exact Finset.subset_union_right
  · intro x hx
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    have hxb : x ≠ b := fun h => hb (h ▸ hx)
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    simp [insert, hxa, hxb, hxc]

end Partial

/-- Complete a partial triangle partition by meeting the countably many tasks
"cover this point". Fresh partners may depend on the entire finite state. -/
theorem complete [Countable G] (allowed : G → G → Prop)
    (fresh : ∀ (F : Finset G) (a : G), a ∉ F → ∃ b c,
      b ∉ F ∧ c ∉ F ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a*c*b = 1 ∧
      allowed a c ∧ allowed b a ∧ allowed c b) :
    ∃ s : G → G, (∀ x, s (s (s x)) = x) ∧
      (∀ x, x * s (s x) * s x = 1) ∧ ∀ x, allowed x (s (s x)) := by
  classical
  obtain ⟨C, hchain, _, _, hcover⟩ := exists_greedy_chain
    (fun x => {p : Partial allowed | x ∈ p.carrier}) (fun p a => by
      by_cases ha : a ∈ p.carrier
      · exact ⟨p, le_rfl, ha⟩
      obtain ⟨b,c,hb,hc,hab,hac,hbc,ht,hA,hB,hC⟩ := fresh p.carrier a ha
      refine ⟨p.insert a b c ha hb hc hab hac hbc ht hA hB hC,
        Partial.le_insert .., ?_⟩
      simp [Partial.insert]) (Partial.empty : Partial allowed)
  choose p hpC hp using hcover
  let s := fun x => (p x).turn x
  have agree (q : Partial allowed) (hq : q ∈ C) (x : G) (hx : x ∈ q.carrier) :
      s x = q.turn x := by
    rcases eq_or_ne q (p x) with h | h
    · simp [s, ← h]
    rcases hchain hq (hpC x) h with h | h
    · exact h.2 x hx
    · exact (h.2 x (hp x)).symm
  have twice (q : Partial allowed) (hq : q ∈ C) (x : G) (hx : x ∈ q.carrier) :
      s (s x) = q.turn (q.turn x) := by
    rw [agree q hq x hx, agree q hq _ (q.closed x hx)]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x
    rw [twice (p x) (hpC x) x (hp x),
      agree (p x) (hpC x) _ ((p x).closed _ ((p x).closed x (hp x)))]
    exact (p x).cube x (hp x)
  · intro x
    rw [twice (p x) (hpC x) x (hp x), agree (p x) (hpC x) x (hp x)]
    exact (p x).triangle x (hp x)
  · intro x
    rw [twice (p x) (hpC x) x (hp x)]
    exact (p x).control x (hp x)

end
end Parastrophes.TriangleCompletion
