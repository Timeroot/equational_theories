import equational_theories.Parastrophes.Equation1370Image

/-!
# Structural consequences of the longer division-image identities

The exact image of E1370 has a longer defining law, but forgetting part of
that law still gives useful arrows into the numbered catalogue. The operation
is unchanged in this final weakening, so recoverability is preserved.
-/
namespace Law.MagmaLaw
open Parastrophes

/-- E1370's left-division image satisfies E127. Its original multiplication
is recovered by `(x*x)*y` in that division operation, on arbitrary carriers. -/
theorem termStructural1370_127 : Law127.TermStructuralFrom Law1370 := by
  have ht : leftImage1370.TermStructuralFrom Law1370 :=
    characterizes_termStructural_all Catalogue.left_characterizes1370_all_long
      (uniformTermWitness_recovery Catalogue.left_term1370_all)
  have hw : leftImage1370.implies Law127 := by
    intro G M hM
    exact (@Law127.models_iff G M).mpr ((Eq1370Image.iff_basis M).mp hM).1
  intro G M hM
  exact TermStructural.trans ht (termStructural_of_implies hw) M hM

end Law.MagmaLaw
