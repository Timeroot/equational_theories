import equational_theories.Spectrum.Catalogue
import equational_theories.Spectrum.BVAudit

/-!
Stable axiom-list regression checks for the main proof methods. The stronger
per-theorem `spectrum_assert` checks in Catalogue cover *every* catalogue result;
these guards also pin down representative exact axiom lists for human inspection.
Native computation is allowed only at explicitly tagged finite-check seeds.
-/

/-- info: 'Spectrum.full_492' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.full_492

/-- info: 'Spectrum.full_1682' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.full_1682

/--
info: 'Spectrum.not_two_677' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.native_seed_677_2._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Spectrum.not_two_677

/--
info: 'Spectrum.not_three_1485' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.native_seed_1485_3._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Spectrum.not_three_1485

/-- info: 'Spectrum.spectrum_546_eq_556' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.spectrum_546_eq_556

/-- info: 'Spectrum.Catalogue.exact_1485' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_1485

/-- info: 'Spectrum.Catalogue.exact_2162' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_2162

/--
info: 'Spectrum.not_order_1480_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.native_seed_1480_3._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Spectrum.not_order_1480_3

/--
info: Spectrum.Catalogue.exact_474: Spectrum.Status.Evidence.complete; native checks: 22
-/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_474

/-- info: Spectrum.not_order_1286_5: Spectrum.Status.Evidence.complete; native checks: 49 -/
#guard_msgs in
#spectrum_status Spectrum.not_order_1286_5

/--
info: 'Spectrum.Catalogue.exact_1685' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.native_seed_1685_2._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_1685

-- Knuth's cardinality obstruction is now proved by explicit bijections.
/-- info: 'Spectrum.Catalogue.exact_168' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_168

/-- info: 'Spectrum.NoteWitness.model_1486_11' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.NoteWitness.model_1486_11

/-- info: 'Spectrum.NoteWitness.model_1486_13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.NoteWitness.model_1486_13

/-- info: 'Spectrum.NoteWitness.model_1486_21' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.NoteWitness.model_1486_21
