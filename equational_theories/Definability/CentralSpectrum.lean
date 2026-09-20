import equational_theories.Spectrum.Definability
import equational_theories.Spectrum.CentralCardinality
import equational_theories.Spectrum.BookendCardinality
import equational_theories.Spectrum.WeakCentralCardinality
import equational_theories.Spectrum.Generated.CentralWitnesses
import equational_theories.Definability.Central1483OrderEleven

/-!
# Nonsquare E1486 models obstruct definability

The eleven-element model of E1486 separates it from E167, E168, E1483, and E1485 even
for finite first-order definability, hence for all eight definability variants.
No symmetry or recovery requirement is needed: the target operation cannot exist
on this carrier. E1485 is excluded by the general theorem that two is the only
possible prime order of a weak central groupoid.
The E1483 exclusion combines ordinary normalization proofs with sixteen explicit
LRAT certificate checks.
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

theorem Equation1485_not_definableFromFin_Equation1486_spectrum :
    ¬ Law1485.DefinableFromFin Law1486 := by
  intro h
  exact Spectrum.not_order_1485_11
    ((subspectral_of_definableFin h).hasModel Spectrum.NoteWitness.model_1486_11)

theorem Equation1483_not_definableFromFin_Equation1486_spectrum :
    ¬ Law1483.DefinableFromFin Law1486 := by
  intro h
  exact Spectrum.not_order_1483_11
    ((subspectral_of_definableFin h).hasModel Spectrum.NoteWitness.model_1486_11)

/-- info: 'Equation1483_not_definableFromFin_Equation1486_spectrum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Magma.Central1483.Refutation.checkRank10Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank10Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank2Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank3Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank4Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank4Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank5Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank5Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank6Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank6Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank7Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank7Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank8Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank8Zero1._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank9Zero0._native.native_decide.ax_1_1,
 Magma.Central1483.Refutation.checkRank9Zero1._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms Equation1483_not_definableFromFin_Equation1486_spectrum

/-- info: 'Equation167_not_definableFromFin_Equation1486_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation167_not_definableFromFin_Equation1486_spectrum

/-- info: 'Equation168_not_definableFromFin_Equation1486_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation168_not_definableFromFin_Equation1486_spectrum

/-- info: 'Equation1485_not_definableFromFin_Equation1486_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1485_not_definableFromFin_Equation1486_spectrum
