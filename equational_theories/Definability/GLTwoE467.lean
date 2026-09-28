import equational_theories.Definability.GLTwoE63
import Mathlib.Algebra.Field.ZMod

/-!
The scalar E467 model over `𝔽₄₁²` supplies a finite FO obstruction to E63:
every linear automorphism preserves this model, whereas an equivariant E63
operation would require a root of `t⁵ + t⁴ + 1` in `𝔽₄₁`.
-/

namespace Definability.GLTwoE467

instance : Fact (Nat.Prime 41) := ⟨by decide⟩

abbrev K := ZMod 41
abbrev Carrier := K × K

abbrev source : Magma Carrier where
  op x y := (4 * x.1 + 32 * y.1, 4 * x.2 + 32 * y.2)

theorem source_law : @Equation467 Carrier source := by
  have hc0 : (1179652 : K) = 0 := by decide
  have hc1 : (4224 : K) = 1 := by decide
  intro x y
  apply Prod.ext
  · change x.1 = 4*y.1 + 32*(4*x.1 + 32*(4*x.1 + 32*(4*y.1+32*y.1)))
    ring_nf
    rw [hc0, hc1]
    simp
  · change x.2 = 4*y.2 + 32*(4*x.2 + 32*(4*x.2 + 32*(4*y.2+32*y.2)))
    ring_nf
    rw [hc0, hc1]
    simp

theorem no_root : ¬ ∃ d : K, d ^ 5 + d ^ 4 + 1 = 0 := by decide

theorem two_ne_zero : (2 : K) ≠ 0 := by decide

open Law Law.MagmaLaw

theorem Equation63_not_definableFromFin_Equation467 :
    ¬ Law63.DefinableFromFin Law467 :=
  GLTwoE63.not_definableFromFin (K := K) 4 32
    ((@Law467.models_iff Carrier source).mpr source_law) two_ne_zero
    (fun d hd => no_root ⟨d, hd⟩)

/-- info: 'Definability.GLTwoE467.Equation63_not_definableFromFin_Equation467' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Equation63_not_definableFromFin_Equation467

end Definability.GLTwoE467
