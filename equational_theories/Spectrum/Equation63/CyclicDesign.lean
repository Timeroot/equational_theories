import equational_theories.Spectrum.Equation63.Transversal

/-! A TD(8,q) over the cyclic ring whenever q is coprime to 30. -/
namespace Spectrum.E63
open Classical

variable {R : Type*} [CommRing R] [Finite R]

def lineCoord (c : Fin 7 → R) (t : R × R) : Groups → R
  | none => t.2
  | some i => t.1 + c i * t.2

omit [Finite R] in
theorem line_pair_injective (c : Fin 7 → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (i j : Groups) (hne : i ≠ j) :
    Function.Injective (fun t => (lineCoord c t i, lineCoord c t j)) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  cases i with
  | none =>
    cases j with
    | none => exact (hne rfl).elim
    | some j =>
      change b = b' at h1
      change a + c j * b = a' + c j * b' at h2
      exact Prod.ext (by rw [h1] at h2; exact add_right_cancel h2) h1
  | some i =>
    cases j with
    | none =>
      change b = b' at h2
      change a + c i * b = a' + c i * b' at h1
      exact Prod.ext (by rw [h2] at h1; exact add_right_cancel h1) h2
    | some j =>
      change a + c i * b = a' + c i * b' at h1
      change a + c j * b = a' + c j * b' at h2
      obtain ⟨u, heq⟩ := hu i j (fun h => hne (congrArg some h))
      have hz : (c i - c j) * (b-b') = 0 := by linear_combination h1 - h2
      rw [← heq] at hz
      have hb : b = b' := sub_eq_zero.mp ((Units.mul_right_eq_zero u).mp hz)
      exact Prod.ext (by rw [hb] at h1; exact add_right_cancel h1) hb

noncomputable def cyclicDesign (c : Fin 7 → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j)) : Transversal Groups R (R × R) where
  coord := lineCoord c
  pair i j hne x y := by
    have hi := line_pair_injective c hu i j hne
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hi) (x,y)
    refine ⟨t, ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩, ?_⟩
    intro u hu
    exact hi ((Prod.ext hu.1 hu.2).trans ht.symm)

theorem cyclic_units (q : ℕ) (hq : q.Coprime 60) (i j : Fin 7) (hij : i ≠ j) :
    IsUnit ((i.val : ZMod q) - (j.val : ZMod q)) := by
  have hu (k : ℕ) (hk : k ∣ 60) : IsUnit (k : ZMod q) :=
    (ZMod.isUnit_iff_coprime k q).mpr (hq.symm.of_dvd_left hk)
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num
  all_goals exact hu _ (by decide)

noncomputable def designZMod (q : ℕ) [NeZero q] (hq : q.Coprime 60) :
    Transversal Groups (ZMod q) (ZMod q × ZMod q) :=
  cyclicDesign (fun i => (i.val : ZMod q)) (cyclic_units q hq)

end Spectrum.E63
