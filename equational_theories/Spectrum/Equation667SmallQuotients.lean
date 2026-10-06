import equational_theories.Spectrum.Equation667ConstantDiagonal

/-! Idempotents in the two- and four-element E667 models, without enumerating
multiplication tables. The only finite checks concern unary permutations. -/

namespace Spectrum.E667.SmallQuotients

private theorem period_two : ∀ p : Fin 2 → Fin 2, Function.Injective p →
    ∀ x, p x = x ∨ p (p x) = x := by decide +kernel

private theorem period_four_fixed : ∀ p : Fin 4 → Fin 4, Function.Injective p →
    p 0 = 0 → ∀ x, p x = x ∨ p (p x) = x ∨ p (p (p x)) = x := by
  set_option synthInstance.maxSize 1000 in
    decide +kernel

theorem exists_idempotent_two [Magma (Fin 2)] (h : Equation667 (Fin 2)) :
    ∃ x : Fin 2, x ◇ x = x := by
  rcases period_two (fun y => (0 : Fin 2) ◇ y) (E667883.left_injective667 h 0) 0
    with h1 | h2
  · exact ⟨0, h1⟩
  · exact ⟨0 ◇ 0, two_cycle_square_idempotent h 0 h2⟩

/-- A Latin square has a row with a fixed point. At order four all other
cycles of that row have length at most three, and either short-cycle lemma
produces an idempotent. -/
theorem exists_idempotent_four [Magma (Fin 4)] (h : Equation667 (Fin 4)) :
    ∃ x : Fin 4, x ◇ x = x := by
  have hs : Function.Surjective (fun a : Fin 4 => a ◇ 0) :=
    Finite.injective_iff_surjective.mp (E667883.right_injective667 h 0)
  obtain ⟨a, ha⟩ := hs 0
  rcases period_four_fixed (fun y => a ◇ y) (E667883.left_injective667 h a) ha a
    with h1 | h2 | h3
  · exact ⟨a, h1⟩
  · exact ⟨a ◇ a, two_cycle_square_idempotent h a h2⟩
  · exact ⟨a, three_cycle_implies_idempotent h a h3⟩

private theorem transfer {A : Type*} [Magma A] [Finite A] {n : ℕ}
    (h : Equation667 A) (hc : Nat.card A = n)
    (hn : ∀ M : Magma (Fin n), @Equation667 (Fin n) M → ∃ x, M.op x x = x) :
    ∃ x : A, x ◇ x = x := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let E : A ≃ Fin n := Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let M := (inferInstance : Magma A)
  let N := M.relabel E
  letI : Magma (Fin n) := N
  let e : MagmaEquiv A (Fin n) := M.relabelEquiv E
  have he := (Law.satisfies_equiv e).mp ((@Law667.models_iff A M).mpr h)
  obtain ⟨b, hb⟩ := hn N ((@Law667.models_iff (Fin n) N).mp he)
  refine ⟨e.symm b, ?_⟩
  calc
    e.symm b ◇ e.symm b = e.symm (N.op b b) := (e.symm.map_op b b).symm
    _ = e.symm b := congrArg e.symm hb

/-- The small-order idempotent result on arbitrary finite carriers. -/
theorem exists_idempotent_of_card {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hc : Nat.card A = 2 ∨ Nat.card A = 4) :
    ∃ x : A, x ◇ x = x := by
  rcases hc with h2 | h4
  · exact transfer h h2 (fun M hm => @exists_idempotent_two M hm)
  · exact transfer h h4 (fun M hm => @exists_idempotent_four M hm)

spectrum_assert exists_idempotent_two complete
spectrum_assert exists_idempotent_four complete
spectrum_assert exists_idempotent_of_card complete

end Spectrum.E667.SmallQuotients
