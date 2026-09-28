import equational_theories.Spectrum.QuasigroupSix

/-! Finite E667 and E883 magmas are quasigroups. -/

namespace Spectrum.E667883

variable {A : Type*} [Magma A]

theorem left_surjective667 (h : Equation667 A) (a : A) :
    Function.Surjective (fun b => a ◇ b) := by
  intro b
  exact ⟨b ◇ ((b ◇ b) ◇ a), (h b a).symm⟩

theorem left_injective667 [Finite A] (h : Equation667 A) (a : A) :
    Function.Injective (fun b => a ◇ b) :=
  Finite.injective_iff_surjective.mpr (left_surjective667 h a)

theorem right_injective667 [Finite A] (h : Equation667 A) (b : A) :
    Function.Injective (fun a => a ◇ b) := by
  intro a c hac
  let x := a ◇ b
  have ha : x ◇ ((x ◇ x) ◇ a) = b := by
    apply left_injective667 h a
    exact (h x a).symm
  have hc : x ◇ ((x ◇ x) ◇ c) = b := by
    apply left_injective667 h c
    exact (h x c).symm.trans hac
  exact left_injective667 h (x ◇ x) (left_injective667 h x (ha.trans hc.symm))

theorem left_surjective883 (h : Equation883 A) (a : A) :
    Function.Surjective (fun b => a ◇ b) := by
  intro b
  exact ⟨(b ◇ a) ◇ (a ◇ a), (h b a).symm⟩

theorem left_injective883 [Finite A] (h : Equation883 A) (a : A) :
    Function.Injective (fun b => a ◇ b) :=
  Finite.injective_iff_surjective.mpr (left_surjective883 h a)

theorem right_injective883 (h : Equation883 A) (b : A) :
    Function.Injective (fun a => a ◇ b) := by
  intro a c hac
  change a ◇ b = c ◇ b at hac
  calc
    a = b ◇ ((a ◇ b) ◇ (b ◇ b)) := h a b
    _ = b ◇ ((c ◇ b) ◇ (b ◇ b)) := by rw [hac]
    _ = c := (h c b).symm

end Spectrum.E667883
