import equational_theories.Spectrum.Equation63.Transversal

/-! Developing a difference matrix gives a transversal design. This isolates
all finite design certificates from the model gluing argument. -/
namespace Spectrum.E63
open Classical
variable {Q : Type*} [AddCommGroup Q] [Finite Q]

def diffCoord (d : Q → Fin 7 → Q) (t : Q × Q) : Groups → Q
  | none => t.2
  | some i => t.1 + d t.2 i

omit [Finite Q] in
theorem diff_pair_injective (d : Q → Fin 7 → Q)
    (hd : ∀ i j, i ≠ j → Function.Injective (fun x => d x i - d x j))
    (i j : Groups) (hne : i ≠ j) :
    Function.Injective (fun t => (diffCoord d t i, diffCoord d t j)) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  cases i with
  | none =>
    cases j with
    | none => exact (hne rfl).elim
    | some j =>
      change b = b' at h1
      change a + d b j = a' + d b' j at h2
      exact Prod.ext (by rw [h1] at h2; exact add_right_cancel h2) h1
  | some i =>
    cases j with
    | none =>
      change b = b' at h2
      change a + d b i = a' + d b' i at h1
      exact Prod.ext (by rw [h2] at h1; exact add_right_cancel h1) h2
    | some j =>
      change a + d b i = a' + d b' i at h1
      change a + d b j = a' + d b' j at h2
      have hz : d b i - d b j = d b' i - d b' j := by
        have hh := congrArg₂ (· - ·) h1 h2
        simpa only [add_sub_add_left_eq_sub] using hh
      have hb := hd i j (fun h => hne (congrArg some h)) hz
      exact Prod.ext (by rw [hb] at h1; exact add_right_cancel h1) hb

noncomputable def differenceDesign (d : Q → Fin 7 → Q)
    (hd : ∀ i j, i ≠ j → Function.Injective (fun x => d x i - d x j)) :
    Transversal Groups Q (Q × Q) where
  coord := diffCoord d
  pair i j hne x y := by
    have hi := diff_pair_injective d hd i j hne
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hi) (x,y)
    refine ⟨t, ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩, ?_⟩
    intro u hu
    exact hi ((Prod.ext hu.1 hu.2).trans ht.symm)

end Spectrum.E63
