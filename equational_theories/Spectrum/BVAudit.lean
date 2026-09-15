import equational_theories.Spectrum.Generated.BV474_4
import equational_theories.Spectrum.Generated.BV1286_5

/-!
Audit of the integrated symmetry-broken size-four and size-five exclusions.
Imported by the main axiom audit; see `docs/spectrum_bv.md` for total timings.
Every individual check and assembled theorem also has a `spectrum_assert`.
-/

/--
info: Spectrum.BitExclusion.not_order_474_4: Spectrum.Status.Evidence.complete; native checks: 21
-/
#guard_msgs in
#spectrum_status Spectrum.BitExclusion.not_order_474_4

/--
info: Spectrum.BitExclusion.not_order_1286_5: Spectrum.Status.Evidence.complete; native checks: 49
-/
#guard_msgs in
#spectrum_status Spectrum.BitExclusion.not_order_1286_5

/--
info: 'Spectrum.BitExclusion.refute_474_4_0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.BitExclusion.refute_474_4_0._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms Spectrum.BitExclusion.refute_474_4_0

/--
info: 'Spectrum.BitExclusion.refute_1286_5_0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.BitExclusion.refute_1286_5_0._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms Spectrum.BitExclusion.refute_1286_5_0

/--
info: 'Spectrum.Symmetry.covers4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.Symmetry.checked4._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Spectrum.Symmetry.covers4

/--
info: 'Spectrum.Symmetry.covers5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Spectrum.Symmetry.checked5._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Spectrum.Symmetry.covers5
