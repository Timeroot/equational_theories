import equational_theories.WeakCentralGroupoids
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Sharp neighbors and rectangular coordinates

A sharp edge is an ordinary edge along which every two-step path is good.
Finite weak central groupoids have sharp predecessors and successors: the mixed
translations form a family of idempotents preserving each other's fixed points.
A sharp edge then gives an exact rectangular decomposition of the carrier.

These are the shared foundations for the general finite spectrum theorem and
the older prime-cardinality argument.
-/

namespace WeakCentralGroupoid

variable {G : Type*} [original : WeakCentralGroupoid G]

/-- Every two-step path starting with this edge is good. -/
def Sharp (a u : G) : Prop := ∀ b, a ◇ (u ◇ b) = u

theorem sharp_dual {e a : G} (h : Sharp e a) (b : G) : (b ◇ e) ◇ a = e := by
  have hw := eqn e b a
  rw [h b] at hw
  exact hw

theorem sharp_of_dual {e a : G} (h : ∀ b, (b ◇ e) ◇ a = e) : Sharp e a := by
  intro b
  have hd := dual_eqn a b e
  rw [h b] at hd
  exact hd

theorem absorption (x y z : G) : x ◇ ((x ◇ y) ◇ (y ◇ z)) = x ◇ y := by
  calc
    x ◇ ((x ◇ y) ◇ (y ◇ z)) =
        (((y ◇ z) ◇ x) ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ (y ◇ z)) := by
      rw [dual_eqn x y z]
    _ = x ◇ y := dual_eqn (x ◇ y) (y ◇ z) x

theorem mixed_idempotent (a b t : G) :
    a ◇ ((a ◇ (t ◇ b)) ◇ b) = a ◇ (t ◇ b) := by
  have hd := dual_eqn (a ◇ (t ◇ b)) b a
  rw [eqn a b t] at hd
  exact hd

theorem mixed_preserves_fixed (a b c u : G) (hu : a ◇ (u ◇ b) = u) :
    a ◇ ((a ◇ (u ◇ c)) ◇ b) = a ◇ (u ◇ c) := by
  have hb := eqn a b u
  rw [hu] at hb
  have hv := absorption (b ◇ a) u c
  rw [hb] at hv
  have hd := dual_eqn (a ◇ (u ◇ c)) b a
  rw [hv] at hd
  exact hd

/-- A finite family of these idempotent transformations has a common fixed point. -/
theorem sharp_successor [Finite G] (a : G) : ∃ u, Sharp a u := by
  classical
  letI := Fintype.ofFinite G
  have aux (s : Finset G) : ∃ u, ∀ b ∈ s, a ◇ (u ◇ b) = u := by
    induction s using Finset.induction_on with
    | empty => exact ⟨a, by simp⟩
    | @insert b s _ ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨a ◇ (u ◇ b), ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact mixed_idempotent a c u
      · exact mixed_preserves_fixed a c b u (hu c hc)
  obtain ⟨u, hu⟩ := aux Finset.univ
  exact ⟨u, fun b => hu b (Finset.mem_univ b)⟩

theorem sharp_predecessor [Finite G] (a : G) : ∃ e, Sharp e a := by
  let opposite : WeakCentralGroupoid G :=
    { op := fun x y => y ◇ x, eqn := fun x y z => dual_eqn x y z }
  obtain ⟨e, he⟩ := @sharp_successor G opposite _ a
  exact ⟨e, @sharp_of_dual G original e a he⟩

/-- A sharp edge gives an exact rectangular factorization, on arbitrary carriers. -/
def sharpProductEquiv {e a : G} (h : Sharp e a) :
    G ≃ Set.range (a ◇ ·) × Set.range (· ◇ e) where
  toFun x := (⟨a ◇ x, x, rfl⟩, ⟨x ◇ e, x, rfl⟩)
  invFun p := p.1.1 ◇ p.2.1
  left_inv x := by
    have hd := dual_eqn x e (a ◇ e)
    rw [h e] at hd
    exact hd
  right_inv p := by
    obtain ⟨⟨u, x, rfl⟩, ⟨v, y, rfl⟩⟩ := p
    apply Prod.ext <;> apply Subtype.ext
    · have hw := eqn (a ◇ x) e y
      rw [h x] at hw
      exact hw
    · have hd := dual_eqn (y ◇ e) a x
      rw [sharp_dual h y] at hd
      exact hd

theorem row_card_dvd [Finite G] (a : G) :
    Nat.card (Set.range (a ◇ ·)) ∣ Nat.card G := by
  obtain ⟨e, he⟩ := sharp_predecessor a
  refine ⟨Nat.card (Set.range (· ◇ e)), ?_⟩
  exact (Nat.card_congr (sharpProductEquiv he)).trans (Nat.card_prod _ _)

end WeakCentralGroupoid
