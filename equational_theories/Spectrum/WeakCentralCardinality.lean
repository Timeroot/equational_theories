import equational_theories.Spectrum.WeakCentral.Basic
import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime cardinalities of weak central groupoids

This module retains the prime-order and constant-row API. The shared
sharp-neighbor and rectangular foundations are in `WeakCentral/Basic.lean`.
-/

open Function

namespace WeakCentralGroupoid

variable {G : Type*} [original : WeakCentralGroupoid G]

theorem prime_row_cases [Finite G] (hp : (Nat.card G).Prime) (a : G) :
    (∃ b, ∀ x, a ◇ x = b) ∨ Bijective (a ◇ ·) := by
  rcases hp.eq_one_or_self_of_dvd _ (row_card_dvd a) with h | h
  · obtain ⟨b, hb⟩ := Nat.card_eq_one_iff_exists.mp h
    exact Or.inl ⟨b.1, fun x => congrArg Subtype.val (hb ⟨a ◇ x, x, rfl⟩)⟩
  · have hv : Bijective (Subtype.val : Set.range (a ◇ ·) → G) :=
      (Nat.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective, h⟩
    have hs : Surjective (a ◇ ·) := by
      intro y
      obtain ⟨⟨_, x, rfl⟩, hx⟩ := hv.2 y
      exact ⟨x, hx⟩
    exact Or.inr ⟨(Finite.injective_iff_surjective).mpr hs, hs⟩

theorem constant_row_column {zero one : G} (h0 : ∀ x, zero ◇ x = one) :
    ∀ x, x ◇ zero = one := by
  have h11 : one ◇ one = zero := by simpa only [h0] using eqn zero zero zero
  have hi (x : G) : one ◇ (x ◇ one) = x := by
    simpa only [h0] using eqn x zero zero
  have hinj : Injective (· ◇ one) := by
    intro x y hxy
    calc
      x = one ◇ (x ◇ one) := (hi x).symm
      _ = one ◇ (y ◇ one) := congrArg (one ◇ ·) hxy
      _ = y := hi y
  intro x
  apply hinj
  calc
    (x ◇ zero) ◇ one = zero := by simpa only [h0] using eqn zero x zero
    _ = one ◇ one := h11.symm

theorem constant_column_row {zero one : G} (h0 : ∀ x, x ◇ zero = one) :
    ∀ x, zero ◇ x = one := by
  let opposite : WeakCentralGroupoid G :=
    { op := fun x y => y ◇ x, eqn := fun x y z => dual_eqn x y z }
  exact @constant_row_column G opposite zero one h0

/-- A bijective row supplies a constant column, with a useful incident edge. -/
theorem constant_column_of_bijective (a : G) (ha : Bijective (a ◇ ·)) :
    ∃ b, b ◇ a = a ∧ ∀ z, z ◇ b = b ◇ b := by
  obtain ⟨t, ht⟩ := ha.2 a
  let b := (t ◇ t) ◇ a
  have hb : b ◇ a = a := by simpa only [ht] using dual_eqn a t t
  refine ⟨b, hb, fun z => ha.1 (ha.1 ?_)⟩
  have hz := eqn a b z
  have hh := eqn a b b
  rw [hb] at hz hh
  exact hz.trans hh.symm

theorem constant_row_unique {zero one b c : G} (h0 : ∀ x, zero ◇ x = one)
    (hb : ∀ x, b ◇ x = c) : b = zero := by
  have hcol := constant_row_column h0
  have hc : c = one := (hb zero).symm.trans (hcol b)
  have h11 : one ◇ one = zero := by simpa only [h0] using eqn zero zero zero
  simpa only [h0, hb, hc, h11] using (eqn b zero zero).symm

theorem bijective_row_unique {zero one a : G} (h0 : ∀ x, zero ◇ x = one)
    (ha : Bijective (a ◇ ·)) : a = one := by
  have hcol := constant_row_column h0
  have h11 : one ◇ one = zero := by simpa only [h0] using eqn zero zero zero
  obtain ⟨b, hb, hc⟩ := constant_column_of_bijective a ha
  have hv : b ◇ b = one := (hc zero).symm.trans (h0 b)
  have hb0 : b = zero := by
    simpa only [h0, hcol, hc, hv, h11] using (dual_eqn b zero zero).symm
  rw [hb0, h0] at hb
  exact hb.symm

/-- Two is the only possible prime cardinality of a finite weak central groupoid. -/
theorem prime_card_eq_two [Finite G] [Nonempty G] (hp : (Nat.card G).Prime) :
    Nat.card G = 2 := by
  classical
  have hconstant : ∃ zero one : G, ∀ x, zero ◇ x = one := by
    let a : G := Classical.arbitrary G
    rcases prime_row_cases hp a with ⟨b, hb⟩ | ha
    · exact ⟨a, b, hb⟩
    · obtain ⟨b, _, hb⟩ := constant_column_of_bijective a ha
      exact ⟨b, b ◇ b, constant_column_row hb⟩
  obtain ⟨zero, one, h0⟩ := hconstant
  have hcases (x : G) : x = zero ∨ x = one := by
    rcases prime_row_cases hp x with ⟨b, hb⟩ | hx
    · exact Or.inl (constant_row_unique h0 hb)
    · exact Or.inr (bijective_row_unique h0 hx)
  have hs : Surjective (fun b : Bool => if b then one else zero) := by
    intro x
    rcases hcases x with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  have hle : Nat.card G ≤ 2 := by
    simpa using Nat.card_le_card_of_surjective _ hs
  exact hle.antisymm hp.two_le

end WeakCentralGroupoid

/-- info: 'WeakCentralGroupoid.prime_card_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WeakCentralGroupoid.prime_card_eq_two

namespace Spectrum

/-- E1485 admits no odd prime order. -/
theorem prime_order_1485 {p : ℕ} (hp : p.Prime) (h : Law1485.HasModel p) : p = 2 := by
  obtain ⟨M, hM⟩ := h
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : WeakCentralGroupoid (Fin p) :=
    { op := M.op
      eqn := fun x y z => ((@Law1485.models_iff (Fin p) M).mp hM x y z).symm }
  simpa using WeakCentralGroupoid.prime_card_eq_two (G := Fin p) (by simpa using hp)

theorem not_order_1485_11 : ¬ Law1485.HasModel 11 := by
  intro h
  have := prime_order_1485 (by decide : Nat.Prime 11) h
  contradiction

theorem not_order_1485_13 : ¬ Law1485.HasModel 13 := by
  intro h
  have := prime_order_1485 (by decide : Nat.Prime 13) h
  contradiction

/-- info: 'Spectrum.prime_order_1485' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_order_1485

/-- info: 'Spectrum.not_order_1485_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_order_1485_11

/-- info: 'Spectrum.not_order_1485_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_order_1485_13

end Spectrum
