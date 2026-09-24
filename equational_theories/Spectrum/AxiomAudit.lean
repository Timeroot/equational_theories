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

/-- info: 'Spectrum.Catalogue.exact_546' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_546

/-- info: 'Spectrum.Catalogue.exact_949' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_949

/-- info: 'Spectrum.Catalogue.exact_895' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_895

/-- info: 'Spectrum.Catalogue.exact_898' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_898

/-- info: 'Spectrum.Catalogue.exact_2789' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_2789

/-- info: 'Spectrum.Catalogue.exact_167' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Catalogue.exact_167

/-- info: 'Spectrum.GaussianRepresentation.module' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.GaussianRepresentation.module

/-- info: 'Spectrum.GaussianRepresentation.affine_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.GaussianRepresentation.affine_formula

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

/-- info: Spectrum.spectrum_115: Spectrum.Status.Evidence.complete; native checks: 2 -/
#guard_msgs in
#spectrum_status Spectrum.spectrum_115

/-- info: Spectrum.spectrum_481: Spectrum.Status.Evidence.complete; native checks: 2 -/
#guard_msgs in
#spectrum_status Spectrum.spectrum_481

/-- info: Spectrum.spectrum_873: Spectrum.Status.Evidence.complete; native checks: 3 -/
#guard_msgs in
#spectrum_status Spectrum.spectrum_873

/-- info: 'Spectrum.Cyclic115.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Cyclic115.law

/-- info: 'Spectrum.Cyclic481.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.Cyclic481.law

/-- info: 'Spectrum.odd_sums_467' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.odd_sums_467

/-- info: Spectrum.loops_667: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.loops_667

/-- info: Spectrum.loops_883: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.loops_883

/-- info: Spectrum.mendelsohn_1719: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.mendelsohn_1719

/-- info: 'Spectrum.spectrum_1719' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.spectrum_1719

/-- info: Spectrum.Catalogue.exact_1719: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_1719

/-- info: Spectrum.Catalogue.exact_1888: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_1888

/-- info: 'Spectrum.idempotent_models_1489' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.idempotent_models_1489

/-- info: Spectrum.idempotent_models_1489: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.idempotent_models_1489

/-- info: Spectrum.Catalogue.exact_1489: Spectrum.Status.Evidence.complete; native checks: 2 -/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_1489

/-- info: Spectrum.Catalogue.exact_2098: Spectrum.Status.Evidence.complete; native checks: 2 -/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_2098

/-- info: 'Spectrum.models_1480' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.models_1480

/-- info: Spectrum.models_1480: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.models_1480

/-- info: Spectrum.Catalogue.exact_1480: Spectrum.Status.Evidence.complete; native checks: 2 -/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_1480

/-- info: Spectrum.Catalogue.exact_2089: Spectrum.Status.Evidence.complete; native checks: 2 -/
#guard_msgs in
#spectrum_status Spectrum.Catalogue.exact_2089

/-- info: Spectrum.Note.finite_1480: Spectrum.Status.Evidence.complete; native checks: 0 -/
#guard_msgs in
#spectrum_status Spectrum.Note.finite_1480

-- The E63 constructive lower bound and tail use no computational or external axioms.
/-- info: 'Spectrum.E63.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.E63.lower

/-- info: 'Spectrum.E63.all_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.E63.all_large
