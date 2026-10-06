import equational_theories.Spectrum.Equation667MedialAffine
import Mathlib.Data.Fintype.Card

/-! A proper submagma of an E667 algebra with bijective squaring occupies
at most one third of the algebra. An idempotent outside the submagma makes
the inequality strict. The proof constructs three disjoint copies directly;
it does not assume a design representation for the original algebra. -/
namespace Spectrum.E667.SubmagmaBound
noncomputable section
variable {Q : Type*} [Magma Q] [Finite Q]
variable (h : Equation667 Q) (S : Set Q)
variable (closed : ∀ x ∈ S, ∀ y ∈ S, x ◇ y ∈ S)

include h closed in
theorem left_mem_iff (x : Q) (hx : x ∈ S) (y : Q) : x ◇ y ∈ S ↔ y ∈ S := by
  constructor
  · intro hy
    let f : S → S := fun z => ⟨x ◇ z, closed x hx z z.property⟩
    have hi : Function.Injective f := fun u v he =>
      Subtype.ext (E667883.left_injective667 h x (congrArg Subtype.val he))
    obtain ⟨z,hz⟩ := Finite.injective_iff_surjective.mp hi ⟨x ◇ y,hy⟩
    have hz' : (z : Q) = y := E667883.left_injective667 h x (congrArg Subtype.val hz)
    exact hz' ▸ z.property
  · exact closed x hx y

def square (hd : Function.Bijective (fun x : Q => x ◇ x)) : Q ≃ Q :=
  Equiv.ofBijective _ hd

def column (hd : Function.Bijective (fun x : Q => x ◇ x)) (a y : Q) : Q :=
  (square hd).symm ((MedialAffine.right h y).symm a)

theorem column_spec (hd : Function.Bijective (fun x : Q => x ◇ x)) (a y : Q) :
    (column h hd a y ◇ column h hd a y) ◇ y = a := by
  have hh := (square hd).apply_symm_apply ((MedialAffine.right h y).symm a)
  change column h hd a y ◇ column h hd a y = (MedialAffine.right h y).symm a at hh
  rw [hh]
  exact (MedialAffine.right h y).apply_symm_apply a

theorem column_injective (hd : Function.Bijective (fun x : Q => x ◇ x)) (a : Q) :
    Function.Injective (column h hd a) := by
  intro y z he
  apply E667883.left_injective667 h (column h hd a y ◇ column h hd a y)
  exact (column_spec h hd a y).trans (by rw [he]; exact (column_spec h hd a z).symm)

def threeCopies (hd : Function.Bijective (fun x : Q => x ◇ x)) (a : Q) :
    S ⊕ (S ⊕ S) → Q
  | .inl x => x
  | .inr (.inl x) => x ◇ a
  | .inr (.inr y) => column h hd a y ◇ a

include closed in
theorem threeCopies_injective (hd : Function.Bijective (fun x : Q => x ◇ x))
    (a : Q) (ha : a ∉ S) : Function.Injective (threeCopies h S hd a) := by
  have first (x : S) : x.val ◇ a ∉ S := fun hh =>
    ha ((left_mem_iff h S closed x x.property a).mp hh)
  have second (y : S) : column h hd a y ◇ a ∉ S := by
    intro hb
    let x := column h hd a y
    have hh : x = y.val ◇ (x ◇ a) := by
      simpa only [x, column_spec h hd a y] using h x y
    have hx : x ∈ S := hh ▸ closed y y.property (x ◇ a) hb
    exact ha ((column_spec h hd a y) ▸ closed (x ◇ x) (closed x hx x hx) y y.property)
  have third (x y : S) : x.val ◇ a ≠ column h hd a y ◇ a := by
    intro he
    have hx : x.val = column h hd a y := E667883.right_injective667 h a he
    have hc := column_spec h hd a y
    rw [← hx] at hc
    exact ha (hc ▸ closed (x ◇ x) (closed x x.property x x.property) y y.property)
  intro u v he
  rcases u with x | x | x <;> rcases v with y | y | y <;>
    simp only [threeCopies] at he
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact False.elim (first y (he ▸ x.property))
  · exact False.elim (second y (he ▸ x.property))
  · exact False.elim (first x (he.symm ▸ y.property))
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (E667883.right_injective667 h a he))
  · exact False.elim (third x y he)
  · exact False.elim (second x (he.symm ▸ y.property))
  · exact False.elim (third y x he.symm)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext
      (column_injective h hd a (E667883.right_injective667 h a he)))

include h closed in
/-- The usual orthogonal-Latin-square subalgebra bound, proved directly
from E667 and bijectivity of squaring. -/
theorem card_bound (hd : Function.Bijective (fun x : Q => x ◇ x))
    (a : Q) (ha : a ∉ S) : 3 * Nat.card S ≤ Nat.card Q := by
  have hh := Nat.card_le_card_of_injective _ (threeCopies_injective h S closed hd a ha)
  simp only [Nat.card_sum] at hh
  omega

theorem avoids_idempotent (hd : Function.Bijective (fun x : Q => x ◇ x))
    (a : Q) (ha : a ∉ S) (haa : a ◇ a = a) (u : S ⊕ (S ⊕ S)) :
    threeCopies h S hd a u ≠ a := by
  rcases u with x | x | y
  · exact fun he => ha (he ▸ x.property)
  · intro he
    have hx : x.val = a := E667883.right_injective667 h a (he.trans haa.symm)
    exact ha (hx ▸ x.property)
  · intro he
    have hx : column h hd a y = a := E667883.right_injective667 h a (he.trans haa.symm)
    have hh := column_spec h hd a y
    rw [hx,haa] at hh
    have hy : y.val = a := E667883.left_injective667 h a (hh.trans haa.symm)
    exact ha (hy ▸ y.property)

include h closed in
/-- An outside idempotent contributes a fourth, single point disjoint
from the three copies of the submagma. -/
theorem strict_card_bound (hd : Function.Bijective (fun x : Q => x ◇ x))
    (a : Q) (ha : a ∉ S) (haa : a ◇ a = a) : 3 * Nat.card S < Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype S := Fintype.ofFinite S
  have hh := Fintype.card_lt_of_injective_not_surjective (threeCopies h S hd a)
    (threeCopies_injective h S closed hd a ha) (by
      intro hs
      obtain ⟨u,hu⟩ := hs a
      exact avoids_idempotent h S hd a ha haa u hu)
  simp only [← Nat.card_eq_fintype_card, Nat.card_sum] at hh
  omega

include h closed in
theorem idempotent_card_bound (idem : ∀ x : Q, x ◇ x = x)
    (a : Q) (ha : a ∉ S) : 3 * Nat.card S < Nat.card Q := by
  apply strict_card_bound h S closed _ a ha (idem a)
  simpa only [idem] using Function.bijective_id

spectrum_assert card_bound complete
spectrum_assert strict_card_bound complete
spectrum_assert idempotent_card_bound complete
end
end Spectrum.E667.SubmagmaBound
