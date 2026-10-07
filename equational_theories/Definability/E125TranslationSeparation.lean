import equational_theories.Definability.CloneTraps
import equational_theories.Definability.E63Family
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# A seven-element obstruction to idempotent squaring

On `ZMod 7`, the operation `x*y=4x+4y+1` satisfies E125 and commutes with
all translations. Every term interpretation inherits these translations.
For a translation-invariant operation `q`, its square is `q(x,x)=q(0,0)+x`.
If this square is idempotent (E3659), then `q(0,0)=0`, so `q` is idempotent.
Every term formed from `q` is then idempotent too. It cannot recover the
original operation, whose square sends `0` to `1`.
-/

namespace TranslationSquare
variable {G : Type} [AddGroup G] (N : Magma G)

/-- A translation-invariant operation with idempotent squaring is idempotent. -/
theorem idempotent (hN : ∀ x y a, N.op (x+a) (y+a) = N.op x y+a)
    (h : @Equation3659 G N) : Magma.DiagFixed N.op := by
  have h0 : N.op 0 0 = 0 := by
    have hh := h 0
    change N.op 0 0 = N.op (N.op 0 0) (N.op 0 0) at hh
    have ht := hN 0 0 (N.op 0 0)
    simp only [zero_add] at ht
    rw [ht] at hh
    exact (add_left_cancel (show N.op 0 0 + 0 = N.op 0 0 + N.op 0 0 by simpa using hh)).symm
  intro x
  have ht := hN 0 0 x
  simpa [h0] using ht

end TranslationSquare

namespace E125Translation

@[reducible] def model : Magma (ZMod 7) := ⟨fun x y => 4*x+4*y+1⟩

theorem equation125 : @Equation125 (ZMod 7) model := by decide

theorem equivariant (a : ZMod 7) : Magma.Equivariant (fun x => x+a) model.op := by
  intro x y
  change 4*(x+a)+4*(y+a)+1=(4*x+4*y+1)+a
  ring_nf
  rw [show (8 : ZMod 7) = 1 by decide, mul_one]

theorem no_recovery : ¬ Law.MagmaLaw.TermStructuralOnMagma Law3659 model := by
  rintro ⟨N, hN, hforward, hback⟩
  have ht (a : ZMod 7) := (Magma.Equivariant.isCloneInvariant (equivariant a)).of_termDefinable hforward
  have hi : Magma.DiagFixed N.op := TranslationSquare.idempotent N
    (fun x y a => ht a x y) ((@Law3659.models_iff (ZMod 7) N).mp hN)
  have hm := hi.isCloneInvariant.of_termDefinable hback
  have h0 := hm 0
  change (4*(0 : ZMod 7)+4*0+1) = 0 at h0
  norm_num at h0
  exact (by decide : (1 : ZMod 7) ≠ 0) h0

end E125Translation

open Law Law.MagmaLaw

theorem Equation3659_not_termStructuralFromFin_Equation125_translation :
    ¬ Law3659.TermStructuralFromFin Law125 := by
  intro h
  exact E125Translation.no_recovery (h E125Translation.model
    ((@Law125.models_iff (ZMod 7) E125Translation.model).mpr E125Translation.equation125))

spectrum_assert Equation3659_not_termStructuralFromFin_Equation125_translation complete

spectrum_assert TranslationSquare.idempotent complete
spectrum_assert E125Translation.equation125 complete
