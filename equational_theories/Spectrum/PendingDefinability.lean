import equational_theories.Spectrum.Definability
import equational_theories.Spectrum.NotePending
import equational_theories.Spectrum.Generated.CentralWitnesses

/-!
# Compatibility name for a formerly pending spectrum consequence

The prime-order theorem now completes this negative. The board seed is in
`Definability/CentralSpectrum.lean`; this historical name remains available to
spectrum clients, with its completed status and standard axioms checked below.
-/

namespace Spectrum.Pending

/-- The prime-order exclusion at 11 separates E1486 from E1485 in all eight variants. -/
theorem not_definableFin_1486_1485 : ¬ Law1485.DefinableFromFin Law1486 := by
  intro h
  exact not_order_1485_11
    ((Law.MagmaLaw.subspectral_of_definableFin h).hasModel NoteWitness.model_1486_11)

spectrum_assert not_definableFin_1486_1485 complete

/-- info: 'Spectrum.Pending.not_definableFin_1486_1485' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_definableFin_1486_1485

end Spectrum.Pending
