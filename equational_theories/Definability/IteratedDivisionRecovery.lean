import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import equational_theories.Spectrum.Status
import Mathlib.Logic.Function.Iterate

/-!
# Recovering iterated one-sided divisions

If `y * L_x^(k+1)(y) = x`, define `x □ y = L_x^(k+1)(y)`.
Then `L_y R□_y = id`, hence `L□_y (R□_y)^(k+1) = id`.
The original operation is recovered by
`x*y = x □ ((R□_x)^k y)`, since `L_x^(k+1) (R□_x)^k = L_x`.
No finiteness or two-sided cancellation is needed. The case `k+1=3`
upgrades the known E464 → E1289 construction to term-structural.
-/

namespace IteratedDivision
variable {G : Type} [Magma G]

@[reducible] def companion (k : ℕ) : Magma G :=
  ⟨fun x y => (fun z => x ◇ z)^[k] y⟩

/-- A one-sided division identity is enough to recover the original operation. -/
theorem recover (k : ℕ) (h : ∀ x y : G, y ◇ (fun z => x ◇ z)^[k+1] y = x)
    (x y : G) :
    (companion (k+1)).op x ((fun z => (companion (k+1)).op z x)^[k] y) = x ◇ y := by
  have hi : Function.LeftInverse (fun z => x ◇ z)
      (fun z => (companion (k+1)).op z x) := fun z => h z x
  change (fun z => x ◇ z)^[k+1] ((fun z => (companion (k+1)).op z x)^[k] y) = _
  rw [Function.iterate_succ_apply', hi.iterate k y]

/-- The new row is the old row's `k`th power, so `k` cancellations prove its law. -/
theorem companion_law (k : ℕ) (h : ∀ x y : G, y ◇ (fun z => x ◇ z)^[k] y = x)
    (x y : G) :
    (companion k).op y ((fun z => (companion k).op z y)^[k] x) = x := by
  have hi : Function.LeftInverse (fun z => y ◇ z)
      (fun z => (companion k).op z y) := fun z => h z y
  exact hi.iterate k x

theorem companion464 (h : Equation464 G) : @Equation1289 G (companion 3) := by
  intro x y
  exact (companion_law 3 (fun x y => (h x y).symm) x y).symm

theorem recover464 (h : Equation464 G) (x y : G) :
    (companion 3).op x ((companion 3).op ((companion 3).op y x) x) = x ◇ y :=
  recover 2 (fun x y => (h x y).symm) x y

end IteratedDivision

open FirstOrder.Language Law Law.MagmaLaw
private abbrev tm {G : Type} (a b : (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2)) :
    (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2) :=
  Functions.apply₂ (Sum.inl ()) a b

theorem Equation1289_termStructuralFrom_Equation464_iteratedDivision :
    Law1289.TermStructuralFrom Law464 := by
  intro G M hM
  have h : Equation464 G := Law464.models_iff.mp hM
  refine ⟨IteratedDivision.companion 3, ?_, ?_, ?_⟩
  · exact (@Law1289.models_iff G (IteratedDivision.companion 3)).mpr (IteratedDivision.companion464 h)
  · exact ⟨tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), rfl⟩
  · exact ⟨tm (Term.var 0) (tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)),
      funext fun z => (IteratedDivision.recover464 h (z 0) (z 1)).symm⟩

spectrum_assert Equation1289_termStructuralFrom_Equation464_iteratedDivision complete

spectrum_assert IteratedDivision.recover complete
spectrum_assert IteratedDivision.companion_law complete
