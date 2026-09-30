import equational_theories.Spectrum.Equation677.DesignWitnesses

/-! Small seeds and affine-certificate interpretation for the effective E677 tail.
The three table seeds are from PR #6. Products, fourth powers, and scalar models
reuse the existing spectrum constructions. -/
namespace Spectrum.E677.EffectiveTail
open Law Law.MagmaLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def affineOK (m a b : Nat) : Bool :=
  a * b * (1 + b * b) % m == 1 % m && (a + a * a * b * b + b * b * b) % m == 0

theorem hasModel_of_affineOK {m a b : Nat} (h : affineOK m a b = true) :
    Law677.HasModel m := by
  by_cases hm : m = 0
  · subst m; exact Law677.hasModel_zero
  letI : NeZero m := ⟨hm⟩
  simp only [affineOK, Bool.and_eq_true, beq_iff_eq] at h
  have hx := (ZMod.natCast_eq_natCast_iff (a*b*(1+b*b)) 1 m).mpr h.1
  have hy := (ZMod.natCast_eq_natCast_iff (a+a*a*b*b+b*b*b) 0 m).mpr
    (show (a+a*a*b*b+b*b*b)%m = 0%m by simpa using h.2)
  push_cast at hx hy
  apply (scalar_model (a : ZMod m) (b : ZMod m) ?_ ?_).hasModel
  · convert hx using 1; ring
  · convert hy using 1; ring

theorem hasModel_pow_four (j : Nat) : Law677.HasModel (j^4) := by
  by_cases hj : j = 0
  · subst j; exact Law677.hasModel_zero
  letI : NeZero j := ⟨hj⟩
  exact (quartic j).hasModel

end Spectrum.E677.EffectiveTail
