import equational_theories.Spectrum.SmallPairs
import equational_theories.Spectrum.Generated.Modular
import equational_theories.Spectrum.Generated.NoteWitnesses
import equational_theories.Spectrum.OpenWitnesses
import equational_theories.Spectrum.TwistedGaussian
import equational_theories.Spectrum.Definability

/-! Explicit cardinality obstructions for the remaining possible spectrum merges.
The direction is always positive source → excluded target. These also refute
finite FO-definability, and therefore every stronger arrow. -/
namespace Spectrum.SmallPairs

theorem not_subspectral_of_order {A B : Law.NatMagmaLaw} {n : ℕ}
    (ha : A.HasModel n) (hb : ¬ B.HasModel n) : ¬ A.Subspectral B :=
  fun h => hb (h.hasModel ha)

/-- Order 7 exists for E1110 and is impossible for E670. -/
theorem not_subspectral_1110_670 : ¬ Law1110.Subspectral Law670 :=
  not_subspectral_of_order model_1110_7 not_order_670_7

theorem spectrum_1110_ne_670 : Law1110.spectrum ≠ Law670.spectrum :=
  fun h => not_subspectral_1110_670 h.subset

theorem not_definableFin_1110_670 : ¬ Law670.DefinableFromFin Law1110 :=
  fun h => not_subspectral_1110_670 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1110_670 complete
spectrum_assert spectrum_1110_ne_670 complete
spectrum_assert not_definableFin_1110_670 complete

/-- Order 8 exists for E467 and is impossible for E677. -/
theorem not_subspectral_467_677 : ¬ Law467.Subspectral Law677 :=
  not_subspectral_of_order NoteWitness.model_467_8 not_order_677_8

theorem spectrum_467_ne_677 : Law467.spectrum ≠ Law677.spectrum :=
  fun h => not_subspectral_467_677 h.subset

theorem not_definableFin_467_677 : ¬ Law677.DefinableFromFin Law467 :=
  fun h => not_subspectral_467_677 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_467_677 complete
spectrum_assert spectrum_467_ne_677 complete
spectrum_assert not_definableFin_467_677 complete

/-- Order 8 exists for E467 and is impossible for E1313. -/
theorem not_subspectral_467_1313 : ¬ Law467.Subspectral Law1313 :=
  not_subspectral_of_order NoteWitness.model_467_8 not_order_1313_8

theorem spectrum_467_ne_1313 : Law467.spectrum ≠ Law1313.spectrum :=
  fun h => not_subspectral_467_1313 h.subset

theorem not_definableFin_467_1313 : ¬ Law1313.DefinableFromFin Law467 :=
  fun h => not_subspectral_467_1313 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_467_1313 complete
spectrum_assert spectrum_467_ne_1313 complete
spectrum_assert not_definableFin_467_1313 complete

/-- Order 8 exists for E704 and is impossible for E677. -/
theorem not_subspectral_704_677 : ¬ Law704.Subspectral Law677 :=
  not_subspectral_of_order NoteWitness.model_704_8 not_order_677_8

theorem spectrum_704_ne_677 : Law704.spectrum ≠ Law677.spectrum :=
  fun h => not_subspectral_704_677 h.subset

theorem not_definableFin_704_677 : ¬ Law677.DefinableFromFin Law704 :=
  fun h => not_subspectral_704_677 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_704_677 complete
spectrum_assert spectrum_704_ne_677 complete
spectrum_assert not_definableFin_704_677 complete

/-- Order 8 exists for E704 and is impossible for E1313. -/
theorem not_subspectral_704_1313 : ¬ Law704.Subspectral Law1313 :=
  not_subspectral_of_order NoteWitness.model_704_8 not_order_1313_8

theorem spectrum_704_ne_1313 : Law704.spectrum ≠ Law1313.spectrum :=
  fun h => not_subspectral_704_1313 h.subset

theorem not_definableFin_704_1313 : ¬ Law1313.DefinableFromFin Law704 :=
  fun h => not_subspectral_704_1313 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_704_1313 complete
spectrum_assert spectrum_704_ne_1313 complete
spectrum_assert not_definableFin_704_1313 complete

/-- Order 8 exists for E1279 and is impossible for E677. -/
theorem not_subspectral_1279_677 : ¬ Law1279.Subspectral Law677 :=
  not_subspectral_of_order NoteWitness.model_1279_8 not_order_677_8

theorem spectrum_1279_ne_677 : Law1279.spectrum ≠ Law677.spectrum :=
  fun h => not_subspectral_1279_677 h.subset

theorem not_definableFin_1279_677 : ¬ Law677.DefinableFromFin Law1279 :=
  fun h => not_subspectral_1279_677 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1279_677 complete
spectrum_assert spectrum_1279_ne_677 complete
spectrum_assert not_definableFin_1279_677 complete

/-- Order 8 exists for E1279 and is impossible for E1313. -/
theorem not_subspectral_1279_1313 : ¬ Law1279.Subspectral Law1313 :=
  not_subspectral_of_order NoteWitness.model_1279_8 not_order_1313_8

theorem spectrum_1279_ne_1313 : Law1279.spectrum ≠ Law1313.spectrum :=
  fun h => not_subspectral_1279_1313 h.subset

theorem not_definableFin_1279_1313 : ¬ Law1313.DefinableFromFin Law1279 :=
  fun h => not_subspectral_1279_1313 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1279_1313 complete
spectrum_assert spectrum_1279_ne_1313 complete
spectrum_assert not_definableFin_1279_1313 complete

/-- Order 8 exists for E1516 and is impossible for E677. -/
theorem not_subspectral_1516_677 : ¬ Law1516.Subspectral Law677 :=
  not_subspectral_of_order NoteWitness.model_1516_8 not_order_677_8

theorem spectrum_1516_ne_677 : Law1516.spectrum ≠ Law677.spectrum :=
  fun h => not_subspectral_1516_677 h.subset

theorem not_definableFin_1516_677 : ¬ Law677.DefinableFromFin Law1516 :=
  fun h => not_subspectral_1516_677 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1516_677 complete
spectrum_assert spectrum_1516_ne_677 complete
spectrum_assert not_definableFin_1516_677 complete

/-- Order 8 exists for E1516 and is impossible for E1313. -/
theorem not_subspectral_1516_1313 : ¬ Law1516.Subspectral Law1313 :=
  not_subspectral_of_order NoteWitness.model_1516_8 not_order_1313_8

theorem spectrum_1516_ne_1313 : Law1516.spectrum ≠ Law1313.spectrum :=
  fun h => not_subspectral_1516_1313 h.subset

theorem not_definableFin_1516_1313 : ¬ Law1313.DefinableFromFin Law1516 :=
  fun h => not_subspectral_1516_1313 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1516_1313 complete
spectrum_assert spectrum_1516_ne_1313 complete
spectrum_assert not_definableFin_1516_1313 complete

/-- Order 9 exists for E467 and is impossible for E704. -/
theorem not_subspectral_467_704 : ¬ Law467.Subspectral Law704 :=
  not_subspectral_of_order (odd_square_model_467 3 (by decide)) not_order_704_9

theorem spectrum_467_ne_704 : Law467.spectrum ≠ Law704.spectrum :=
  fun h => not_subspectral_467_704 h.subset

theorem not_definableFin_467_704 : ¬ Law704.DefinableFromFin Law467 :=
  fun h => not_subspectral_467_704 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_467_704 complete
spectrum_assert spectrum_467_ne_704 complete
spectrum_assert not_definableFin_467_704 complete

/-- Order 9 exists for E467 and is impossible for E1279. -/
theorem not_subspectral_467_1279 : ¬ Law467.Subspectral Law1279 :=
  not_subspectral_of_order (odd_square_model_467 3 (by decide)) not_order_1279_9

theorem spectrum_467_ne_1279 : Law467.spectrum ≠ Law1279.spectrum :=
  fun h => not_subspectral_467_1279 h.subset

theorem not_definableFin_467_1279 : ¬ Law1279.DefinableFromFin Law467 :=
  fun h => not_subspectral_467_1279 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_467_1279 complete
spectrum_assert spectrum_467_ne_1279 complete
spectrum_assert not_definableFin_467_1279 complete

/-- Order 9 exists for E677 and is impossible for E704. -/
theorem not_subspectral_677_704 : ¬ Law677.Subspectral Law704 :=
  not_subspectral_of_order NoteWitness.model_677_9 not_order_704_9

theorem spectrum_677_ne_704 : Law677.spectrum ≠ Law704.spectrum :=
  fun h => not_subspectral_677_704 h.subset

theorem not_definableFin_677_704 : ¬ Law704.DefinableFromFin Law677 :=
  fun h => not_subspectral_677_704 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_677_704 complete
spectrum_assert spectrum_677_ne_704 complete
spectrum_assert not_definableFin_677_704 complete

/-- Order 9 exists for E677 and is impossible for E1279. -/
theorem not_subspectral_677_1279 : ¬ Law677.Subspectral Law1279 :=
  not_subspectral_of_order NoteWitness.model_677_9 not_order_1279_9

theorem spectrum_677_ne_1279 : Law677.spectrum ≠ Law1279.spectrum :=
  fun h => not_subspectral_677_1279 h.subset

theorem not_definableFin_677_1279 : ¬ Law1279.DefinableFromFin Law677 :=
  fun h => not_subspectral_677_1279 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_677_1279 complete
spectrum_assert spectrum_677_ne_1279 complete
spectrum_assert not_definableFin_677_1279 complete

/-- Order 9 exists for E1313 and is impossible for E704. -/
theorem not_subspectral_1313_704 : ¬ Law1313.Subspectral Law704 :=
  not_subspectral_of_order SmallPairs.model_1313_9 not_order_704_9

theorem spectrum_1313_ne_704 : Law1313.spectrum ≠ Law704.spectrum :=
  fun h => not_subspectral_1313_704 h.subset

theorem not_definableFin_1313_704 : ¬ Law704.DefinableFromFin Law1313 :=
  fun h => not_subspectral_1313_704 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1313_704 complete
spectrum_assert spectrum_1313_ne_704 complete
spectrum_assert not_definableFin_1313_704 complete

/-- Order 9 exists for E1313 and is impossible for E1279. -/
theorem not_subspectral_1313_1279 : ¬ Law1313.Subspectral Law1279 :=
  not_subspectral_of_order SmallPairs.model_1313_9 not_order_1279_9

theorem spectrum_1313_ne_1279 : Law1313.spectrum ≠ Law1279.spectrum :=
  fun h => not_subspectral_1313_1279 h.subset

theorem not_definableFin_1313_1279 : ¬ Law1279.DefinableFromFin Law1313 :=
  fun h => not_subspectral_1313_1279 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1313_1279 complete
spectrum_assert spectrum_1313_ne_1279 complete
spectrum_assert not_definableFin_1313_1279 complete

/-- Order 9 exists for E1516 and is impossible for E704. -/
theorem not_subspectral_1516_704 : ¬ Law1516.Subspectral Law704 :=
  not_subspectral_of_order OpenWitnesses.model_1516_9 not_order_704_9

theorem spectrum_1516_ne_704 : Law1516.spectrum ≠ Law704.spectrum :=
  fun h => not_subspectral_1516_704 h.subset

theorem not_definableFin_1516_704 : ¬ Law704.DefinableFromFin Law1516 :=
  fun h => not_subspectral_1516_704 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1516_704 complete
spectrum_assert spectrum_1516_ne_704 complete
spectrum_assert not_definableFin_1516_704 complete

/-- Order 9 exists for E1516 and is impossible for E1279. -/
theorem not_subspectral_1516_1279 : ¬ Law1516.Subspectral Law1279 :=
  not_subspectral_of_order OpenWitnesses.model_1516_9 not_order_1279_9

theorem spectrum_1516_ne_1279 : Law1516.spectrum ≠ Law1279.spectrum :=
  fun h => not_subspectral_1516_1279 h.subset

theorem not_definableFin_1516_1279 : ¬ Law1279.DefinableFromFin Law1516 :=
  fun h => not_subspectral_1516_1279 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1516_1279 complete
spectrum_assert spectrum_1516_ne_1279 complete
spectrum_assert not_definableFin_1516_1279 complete

/-- E677 has an eleven-element model; E1313 has none. -/
theorem not_subspectral_677_1313 : ¬ Law677.Subspectral Law1313 :=
  not_subspectral_of_order model_677_11 not_order_1313_11

theorem spectrum_677_ne_1313 : Law677.spectrum ≠ Law1313.spectrum :=
  fun h => not_subspectral_677_1313 h.subset

theorem not_definableFin_677_1313 : ¬ Law1313.DefinableFromFin Law677 :=
  fun h => not_subspectral_677_1313 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_677_1313 complete
spectrum_assert spectrum_677_ne_1313 complete
spectrum_assert not_definableFin_677_1313 complete

/-- E704 has a model at order thirteen; E1279 does not. -/
theorem not_subspectral_704_1279 : ¬ Law704.Subspectral Law1279 :=
  not_subspectral_of_order model_704_13 not_order_1279_13

theorem spectrum_704_ne_1279 : Law704.spectrum ≠ Law1279.spectrum :=
  fun h => not_subspectral_704_1279 h.subset

theorem not_definableFin_704_1279 : ¬ Law1279.DefinableFromFin Law704 :=
  fun h => not_subspectral_704_1279 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_704_1279 complete
spectrum_assert spectrum_704_ne_1279 complete
spectrum_assert not_definableFin_704_1279 complete

end Spectrum.SmallPairs
