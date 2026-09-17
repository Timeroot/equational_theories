import equational_theories.Spectrum.Shapes
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-!
# Central groupoids have square cardinality

An elementary proof of Knuth's cardinality obstruction. For any `a`, the map
`x ↦ (a ◇ x, x ◇ a)` identifies the carrier with `Row a × Col a`.
Moreover every row image is equivalent to every column image, via multiplication.
These equivalences work on infinite carriers too; only the last step uses finiteness.
-/

open Law Law.MagmaLaw
namespace Spectrum.Central

variable {G : Type*} [Magma G] (h : Equation168 G)
include h

private theorem row_cancel {a u : G} (hu : u ∈ Set.range (a ◇ ·)) (b : G) :
    a ◇ (u ◇ b) = u := by
  obtain ⟨w, rfl⟩ := hu
  calc
    a ◇ ((a ◇ w) ◇ b) = ((a ◇ a) ◇ (a ◇ w)) ◇ ((a ◇ w) ◇ b) := by
      rw [← h a a w]
    _ = a ◇ w := (h (a ◇ w) (a ◇ a) b).symm

private theorem col_cancel {b v : G} (hv : v ∈ Set.range (· ◇ b)) (a : G) :
    (a ◇ v) ◇ b = v := by
  obtain ⟨w, rfl⟩ := hv
  calc
    (a ◇ (w ◇ b)) ◇ b = (a ◇ (w ◇ b)) ◇ ((w ◇ b) ◇ (b ◇ b)) := by
      rw [← h b w b]
    _ = w ◇ b := (h (w ◇ b) a (b ◇ b)).symm

/-- All row and column images have the same cardinality. -/
def rowColEquiv (a b : G) : Set.range (a ◇ ·) ≃ Set.range (· ◇ b) where
  toFun u := ⟨u.1 ◇ b, u.1, rfl⟩
  invFun v := ⟨a ◇ v.1, v.1, rfl⟩
  left_inv u := Subtype.ext (row_cancel h u.2 b)
  right_inv v := Subtype.ext (col_cancel h v.2 a)

/-- A central groupoid is in bijection with a row image times a column image. -/
def productEquiv (a : G) : G ≃ Set.range (a ◇ ·) × Set.range (· ◇ a) where
  toFun x := (⟨a ◇ x, x, rfl⟩, ⟨x ◇ a, x, rfl⟩)
  invFun p := p.1.1 ◇ p.2.1
  left_inv x := (h x a a).symm
  right_inv p := Prod.ext (Subtype.ext (row_cancel h p.1.2 p.2.1))
    (Subtype.ext (col_cancel h p.2.2 p.1.1))

theorem card_square [Fintype G] [Nonempty G] : ∃ k : ℕ, Fintype.card G = k ^ 2 := by
  classical
  let a : G := Classical.arbitrary G
  letI := Fintype.ofFinite (Set.range (a ◇ ·))
  letI := Fintype.ofFinite (Set.range (· ◇ a))
  refine ⟨Fintype.card (Set.range (a ◇ ·)), ?_⟩
  rw [Fintype.card_congr (productEquiv h a), Fintype.card_prod,
    ← Fintype.card_congr (rowColEquiv h a a), pow_two]

end Central

theorem orders_168 {n : ℕ} (h : n ∈ Law168.spectrum) : n ∈ squares := by
  obtain ⟨hn, M, hM⟩ := h
  letI := M
  letI : NeZero n := ⟨by omega⟩
  exact ⟨hn, by simpa using Central.card_square (Law168.models_iff.mp hM)⟩

theorem not_order_168_11 : ¬ Law168.HasModel 11 := by
  intro h
  obtain ⟨k, hk⟩ := (orders_168 ⟨by decide, h⟩).2
  have : k ≤ 3 ∨ 4 ≤ k := by omega
  rcases this with h | h <;> nlinarith

/-- info: 'Spectrum.Central.card_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Central.card_square

/-- info: 'Spectrum.not_order_168_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_order_168_11

end Spectrum
