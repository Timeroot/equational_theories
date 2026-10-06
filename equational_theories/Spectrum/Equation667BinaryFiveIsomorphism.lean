import equational_theories.Spectrum.Equation667BinaryFiveProperties
import equational_theories.Spectrum.Equation667BinaryFiveCompleteness

/-! Exactly three isomorphism types in the explicit binary five-point family.
The small normal-form check considers only 32 binary functions on five points.
Nonisomorphism follows from the intrinsic number of commuting ordered pairs. -/
namespace Spectrum.E667.BinaryFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Carrier := ZMod 5 × ZMod 2

def Isomorphic (v w : ZMod 5 → ZMod 2) : Prop :=
  ∃ e : Carrier ≃ Carrier, ∀ x y, e (op v x y) = op w (e x) (e y)

def affineEquiv (a b : ZMod 5) (ha : a ≠ 0) : Carrier ≃ Carrier where
  toFun x := (a * x.1 + b, x.2)
  invFun x := (a⁻¹ * (x.1 - b), x.2)
  left_inv x := by
    apply Prod.ext
    · simp [ha]
    · rfl
  right_inv x := by
    apply Prod.ext
    · simp [ha]
    · rfl

/-- Affine changes of the five base labels, and addition of a constant to
v, preserve the isomorphism type. -/
theorem affine_isomorphism (v w : ZMod 5 → ZMod 2) (a b : ZMod 5) (ha : a ≠ 0)
    (c : ZMod 2) (hv : ∀ i, w (a*i+b) = v i + c) : Isomorphic v w := by
  refine ⟨affineEquiv a b ha, ?_⟩
  intro x y
  apply Prod.ext
  · change a * base x.1 y.1 + b = base (a*x.1+b) (a*y.1+b)
    unfold base
    ring_nf
    reduce_mod_char
  · have hh : 2 * (a*y.1+b) - (a*x.1+b) = a*(2*y.1-x.1)+b := by ring
    change x.2 + y.2 + cocycle v x.1 y.1 = x.2 + y.2 + cocycle w (a*x.1+b) (a*y.1+b)
    simp only [cocycle, hh, hv]
    ring_nf
    reduce_mod_char

def representative (k : Fin 3) (i : ZMod 5) : ZMod 2 := if i.val < k.val then 1 else 0

/-- Up to affine relabelling and complementation, a five-bit function has
support of size zero, one, or two. The check has only 32 possible inputs. -/
private theorem function_normal_form (v : ZMod 5 → ZMod 2) :
    ∃ k : Fin 3, ∃ a b : ZMod 5, a ≠ 0 ∧ ∃ c : ZMod 2,
      ∀ i, representative k (a*i+b) = v i + c := by
  exact (by
    set_option synthInstance.maxSize 2000 in
    decide +kernel : ∀ v : ZMod 5 → ZMod 2,
      ∃ k : Fin 3, ∃ a b : ZMod 5, a ≠ 0 ∧ ∃ c : ZMod 2,
        ∀ i, representative k (a*i+b) = v i + c) v

theorem exists_representative (v : ZMod 5 → ZMod 2) :
    ∃ k : Fin 3, Isomorphic v (representative k) := by
  obtain ⟨k,a,b,ha,c,hc⟩ := function_normal_form v
  exact ⟨k, affine_isomorphism v (representative k) a b ha c hc⟩

abbrev CommutingPairs (v : ZMod 5 → ZMod 2) :=
  {xy : Carrier × Carrier // op v xy.1 xy.2 = op v xy.2 xy.1}

/-- Commuting-pair cardinality is invariant under arbitrary magma
isomorphisms, including ones not specified by the affine construction. -/
theorem commuting_card_congr {v w : ZMod 5 → ZMod 2} (h : Isomorphic v w) :
    Nat.card (CommutingPairs v) = Nat.card (CommutingPairs w) := by
  obtain ⟨e, he⟩ := h
  let E : CommutingPairs v ≃ CommutingPairs w := (Equiv.prodCongr e e).subtypeEquiv (by
    intro xy
    change op v xy.1 xy.2 = op v xy.2 xy.1 ↔ op w (e xy.1) (e xy.2) = op w (e xy.2) (e xy.1)
    rw [← he, ← he]
    exact e.injective.eq_iff.symm)
  exact Nat.card_congr E

/-- The three normal forms have 100, 36, and 68 commuting ordered pairs. -/
theorem representative_commuting_card (k : Fin 3) :
    Nat.card (CommutingPairs (representative k)) = ![100,36,68] k := by
  rw [Nat.card_eq_fintype_card]
  revert k
  decide +kernel

/-- The three representatives remain distinct under all magma isomorphisms. -/
theorem representatives_distinct (i j : Fin 3) (h : Isomorphic (representative i) (representative j)) :
    i = j := by
  have hh := commuting_card_congr h
  rw [representative_commuting_card, representative_commuting_card] at hh
  exact (by decide +kernel : Function.Injective (![100,36,68] : Fin 3 → ℕ)) hh

spectrum_assert exists_representative complete
spectrum_assert representatives_distinct complete
end Spectrum.E667.BinaryFive
