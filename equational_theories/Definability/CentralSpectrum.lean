import equational_theories.Spectrum.Definability
import equational_theories.Spectrum.CentralCardinality
import equational_theories.Spectrum.BookendCardinality
import equational_theories.Spectrum.Generated.CentralWitnesses

/-!
# Nonsquare E1486 models obstruct definability

The eleven-element model of E1486 separates it from both E167 and E168 even
for finite first-order definability, hence for all eight definability variants.
No symmetry or recovery requirement is needed: the target operation cannot exist
on this carrier. E1485 is deliberately absent from this completed-proof module;
its reported SAT exclusions are documented in `Spectrum.NotePending`, and the
consequence awaiting their certificates is in `Spectrum.PendingDefinability`.
-/

open Law Law.MagmaLaw

theorem Equation167_not_definableFromFin_Equation1486_spectrum :
    ¬ Law167.DefinableFromFin Law1486 := by
  intro h
  exact Spectrum.not_order_167_11
    ((subspectral_of_definableFin h).hasModel Spectrum.NoteWitness.model_1486_11)

theorem Equation168_not_definableFromFin_Equation1486_spectrum :
    ¬ Law168.DefinableFromFin Law1486 := by
  intro h
  exact Spectrum.not_order_168_11
    ((subspectral_of_definableFin h).hasModel Spectrum.NoteWitness.model_1486_11)

/-- info: 'Equation167_not_definableFromFin_Equation1486_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation167_not_definableFromFin_Equation1486_spectrum

/-- info: 'Equation168_not_definableFromFin_Equation1486_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation168_not_definableFromFin_Equation1486_spectrum
