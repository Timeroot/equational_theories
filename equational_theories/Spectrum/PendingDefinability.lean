import equational_theories.Spectrum.Definability
import equational_theories.Spectrum.NotePending
import equational_theories.Spectrum.Generated.CentralWitnesses

/-!
# Definability consequences of reported, not yet replayed, spectrum proofs

These are mathematically known negatives awaiting proof integration, NOT open
questions and NOT checked board seeds. Keep them outside `Definability/`, whose
source scanner treats concrete relation theorems as completed evidence.
The pending dependency is pinned to each theorem by both a status assertion and
an axiom guard. No additional `sorry` is introduced for the consequence itself.
-/

namespace Spectrum.Pending

/-- The reported exhaustive exclusion at 11 separates E1486 from E1485 in all eight
variants. No public input/certificate exists; a checked rerun is needed.
The separately reported order-13 exclusion gives the same separation. -/
theorem not_definableFin_1486_1485 : ¬ Law1485.DefinableFromFin Law1486 := by
  intro h
  exact not_order_1485_11
    ((Law.MagmaLaw.subspectral_of_definableFin h).hasModel NoteWitness.model_1486_11)

spectrum_assert not_definableFin_1486_1485 proofAvailable

/-- info: 'Spectrum.Pending.not_definableFin_1486_1485' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_definableFin_1486_1485

end Spectrum.Pending
