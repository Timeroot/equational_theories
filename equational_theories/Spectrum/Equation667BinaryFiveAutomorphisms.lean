import equational_theories.Spectrum.Equation667BinaryFiveIsomorphism

/-! The automorphism groups of the three binary five-point extensions.
The action on the five idempotents determines every automorphism; no
permutations of a ten-element carrier need to be enumerated. -/
namespace Spectrum.E667.BinaryFive
open Classical

abbrev Automorphisms (v : ZMod 5 → ZMod 2) :=
  {e : Carrier ≃ Carrier // ∀ x y, e (op v x y) = op v (e x) (e y)}

private theorem aut_zero (v : ZMod 5 → ZMod 2) (e : Automorphisms v) (i : ZMod 5) :
    (e.val (i,0)).2 = 0 := by
  apply (idempotent_iff v _).mp
  rw [← e.property, square]

noncomputable def baseAut (v : ZMod 5 → ZMod 2) (e : Automorphisms v) : ZMod 5 ≃ ZMod 5 :=
  Equiv.ofBijective (fun i => (e.val (i,0)).1) (by
    apply (Finite.injective_iff_bijective).mp
    intro i j hh
    have he : e.val (i,0) = e.val (j,0) := Prod.ext hh ((aut_zero v e i).trans (aut_zero v e j).symm)
    exact congrArg Prod.fst (e.val.injective he))

/-- An automorphism cannot exchange the two labels in any square fiber:
zero is its unique idempotent. -/
theorem automorphism_shape (v : ZMod 5 → ZMod 2) (e : Automorphisms v)
    (i : ZMod 5) (a : ZMod 2) : e.val (i,a) = (baseAut v e i,a) := by
  have hf : (e.val (i,a)).1 = baseAut v e i := by
    have hh := congrArg Prod.fst (e.property (i,a) (i,a))
    rw [square, square] at hh
    exact hh.symm
  refine Prod.ext hf ?_
  fin_cases a
  · exact aut_zero v e i
  · have bits (b : ZMod 2) : b = 0 ∨ b = 1 := by
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases bits (e.val (i,1)).2 with hz | ho
    · have he : e.val (i,1) = e.val (i,0) := Prod.ext hf (hz.trans (aut_zero v e i).symm)
      have hh := congrArg Prod.snd (e.val.injective he)
      exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hh)
    · exact ho

abbrev BaseAutomorphisms (v : ZMod 5 → ZMod 2) :=
  {e : ZMod 5 ≃ ZMod 5 //
    (∀ i j, e (base i j) = base (e i) (e j)) ∧
    (∀ i j, cocycle v (e i) (e j) = cocycle v i j)}

noncomputable def restrictAut (v : ZMod 5 → ZMod 2) (e : Automorphisms v) : BaseAutomorphisms v :=
  ⟨baseAut v e, by
    constructor
    · intro i j
      have hh := congrArg Prod.fst (e.property (i,0) (j,0))
      rw [show op v (i,0) (j,0) = (base i j,cocycle v i j) by simp [op],
        automorphism_shape, automorphism_shape, automorphism_shape] at hh
      exact hh
    · intro i j
      have hh := congrArg Prod.snd (e.property (i,0) (j,0))
      rw [show op v (i,0) (j,0) = (base i j,cocycle v i j) by simp [op],
        automorphism_shape, automorphism_shape, automorphism_shape] at hh
      simpa only [op, zero_add] using hh.symm⟩

noncomputable def liftAut (v : ZMod 5 → ZMod 2) (e : BaseAutomorphisms v) : Automorphisms v :=
  ⟨Equiv.prodCongr e.val (Equiv.refl _), by
    intro x y
    apply Prod.ext
    · exact e.property.1 x.1 y.1
    · exact congrArg (fun z => x.2+y.2+z) (e.property.2 x.1 y.1).symm⟩

/-- Restriction to the idempotents is a bijection of automorphism sets. -/
noncomputable def automorphismEquiv (v : ZMod 5 → ZMod 2) : Automorphisms v ≃ BaseAutomorphisms v where
  toFun := restrictAut v
  invFun := liftAut v
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,a⟩
    exact (automorphism_shape v e i a).symm
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- The actual automorphism groups have orders 20, 4, and 2. The finite
check runs only over permutations of the five-point quotient. -/
theorem automorphism_card (k : Fin 3) :
    Nat.card (Automorphisms (representative k)) = ![20,4,2] k := by
  rw [Nat.card_congr (automorphismEquiv (representative k)), Nat.card_eq_fintype_card]
  fin_cases k <;> decide +kernel

spectrum_assert automorphism_card complete
spectrum_assert automorphism_shape complete
spectrum_assert automorphismEquiv complete
end Spectrum.E667.BinaryFive
