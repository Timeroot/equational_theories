import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.BooleanReduction
import equational_theories.Subgraph
import equational_theories.Generated.VampireProven.Proofs12
import Mathlib.GroupTheory.PGroup

/-! # The Boolean-group representation and cardinality of E895 -/

namespace Spectrum.BooleanGroup
open Subgraph
variable {G : Type*} [Magma G]

/-- An E895 magma is a Boolean group, with identity the square of any anchor. -/
@[implicit_reducible] def group (h : Equation895 G) (a : G) : CommGroup G := by
  have h1571 := Equation895_implies_Equation1571 G h
  have hc := Equation1571_implies_Equation43 G h1571
  have ha := Equation1571_implies_Equation4512 G h1571
  have hi := Equation1571_implies_Equation16 G h1571
  have hs := Equation1571_implies_Equation40 G h1571
  letI : Mul G := ⟨Magma.op⟩
  letI : One G := ⟨a ◇ a⟩
  letI : Inv G := ⟨id⟩
  exact {
    mul := Magma.op
    one := a ◇ a
    inv := id
    mul_assoc := fun x y z => (ha x y z).symm
    one_mul := fun x => by change (a ◇ a) ◇ x = x; rw [← ha, ← hi]
    mul_one := fun x => by change x ◇ (a ◇ a) = x; rw [hc, ← ha, ← hi]
    inv_mul_cancel := fun x => hs x a
    mul_comm := hc
    npow := npowRec
    zpow := zpowRec }

theorem cardinality [Finite G] (h : Equation895 G) (a : G) :
    ∃ k : ℕ, Nat.card G = 2 ^ k := by
  letI := group h a
  have hp : IsPGroup 2 G := by
    intro x
    refine ⟨1, ?_⟩
    simp only [pow_one, pow_two]
    change x ◇ x = a ◇ a
    exact Equation1571_implies_Equation40 G (Equation895_implies_Equation1571 G h) x a
  exact hp.exists_card_eq

end BooleanGroup

theorem orders_895 {n : ℕ} (h : n ∈ Law895.spectrum) : n ∈ powersTwo := by
  obtain ⟨hn, M, hM⟩ := h
  letI := M
  exact BooleanGroup.cardinality (Law895.models_iff.mp hM) ⟨0, hn⟩ |>.imp
    (fun _ hk => by simpa using hk)

/-- The Boolean-group reduction preserves the carrier, including for infinite magmas. -/
theorem orders_898 {n : ℕ} (h : n ∈ Law898.spectrum) : n ∈ powersTwo := by
  obtain ⟨hn, M, hM⟩ := h
  letI := M
  let a : Fin n := ⟨0, hn⟩
  let M' : Magma (Fin n) := ⟨BooleanReduction.op a⟩
  have h' : @Equation895 (Fin n) M' :=
    @BooleanReduction.law (Fin n) M ((@Law898.models_iff _ M).mp hM) a
  exact orders_895 ⟨hn, M', (@Law895.models_iff _ M').mpr h'⟩

end Spectrum
