import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.QuarticTail.Coverage
import equational_theories.Spectrum.QuarticTail.Arithmetic
import equational_theories.Spectrum.QuarticTail.SmallModels

/-! Explicit idempotent models of E1076 and E1313 at every order at least
107773. The finite interval certificate and the cofinite induction use only
finite fields, direct products, and pairwise balanced design gluing. -/

/-- Positive orders explicitly constructed in the finite quartic design certificate. -/
def Spectrum.quarticTailSeeds : Set ℕ :=
  {n | 0 < n ∧ n ∈ QuarticTail.Generated.orders.values}

namespace Spectrum.QuarticTail
open PBD Law Law.MagmaLaw

theorem finite_1076 : quarticTailSeeds ⊆ Law1076.spectrum := by
  rintro n ⟨hn, hm⟩
  obtain ⟨M⟩ := Generated.model_mem seeds1076 hm
  exact ⟨hn, ⟨⟨M.op⟩, (@Law1076.models_iff _ ⟨M.op⟩).mpr M.law⟩⟩

theorem finite_1313 : quarticTailSeeds ⊆ Law1313.spectrum := by
  rintro n ⟨hn, hm⟩
  obtain ⟨M⟩ := Generated.model_mem seeds1313 hm
  exact ⟨hn, ⟨⟨M.op⟩, (@Law1313.models_iff _ ⟨M.op⟩).mpr M.law⟩⟩

/-- Common construction theorem for the two quartic seed families. -/
theorem models {L : BinaryLaw} (S : Seeds L) (n : ℕ) (hn : 107773 ≤ n) :
    Nonempty (Model L (Fin n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hb : n ≤ 10100000
    · exact Generated.base S n hn hb
    obtain ⟨q,r,hq,hr,hqn,hrn,hrq,hcop,he⟩ :=
      decompose (C := 107773) (n := n) (by decide) (by omega)
    have H := (cyclic17 (by omega : 0 < q) hcop).oneHole
      (L := L) (k := 16) (r := r) (e := 0) (by decide) hrq
      (ih q hqn hq) (ih r hrn hr) (Generated.small16 S)
    simpa only [Nat.add_zero, he] using H

theorem model_1076 (n : ℕ) (hn : 107773 ≤ n) : Law1076.HasModel n := by
  obtain ⟨M⟩ := models seeds1076 n hn
  exact ⟨⟨M.op⟩, (@Law1076.models_iff _ ⟨M.op⟩).mpr M.law⟩

theorem model_1313 (n : ℕ) (hn : 107773 ≤ n) : Law1313.HasModel n := by
  obtain ⟨M⟩ := models seeds1313 n hn
  exact ⟨⟨M.op⟩, (@Law1313.models_iff _ ⟨M.op⟩).mpr M.law⟩

theorem cofinite_1076 : CofiniteSpectrum Law1076 :=
  ⟨107773,fun n hn => ⟨by omega, model_1076 n hn⟩⟩

theorem cofinite_1313 : CofiniteSpectrum Law1313 :=
  ⟨107773,fun n hn => ⟨by omega, model_1313 n hn⟩⟩

spectrum_assert model_1076 complete
spectrum_assert finite_1076 complete
spectrum_assert finite_1313 complete
spectrum_assert model_1313 complete
spectrum_assert cofinite_1076 complete
spectrum_assert cofinite_1313 complete

end Spectrum.QuarticTail

/-- info: 'Spectrum.QuarticTail.model_1076' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.QuarticTail.model_1076
/-- info: 'Spectrum.QuarticTail.model_1313' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.QuarticTail.model_1313
