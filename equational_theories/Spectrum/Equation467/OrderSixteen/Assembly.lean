import equational_theories.Spectrum.Equation467.OrderSixteen.Coverage
import equational_theories.Spectrum.Equation467.OrderSixteen.CertificateEncoding

namespace Spectrum.E467.OrderSixteen

/-- Pure mathematical assembly: any order-sixteen model produces a satisfying
assignment for one of the certificate formulas. -/
theorem exclusion_of_unsat (hu : ∀ r : Ref, (Encoding.natRef r).Unsat) :
    ¬ Law467.HasModel 16 := by
  rintro ⟨M,hM⟩
  let f : Point → Point → Point := @Magma.op _ M
  have hf : Holds f := (@Law467.models_iff _ M).mp hM
  obtain ⟨i,g,hg⟩ := exists_case f hf
  obtain ⟨g,hg,hm⟩ := exists_minimal i g hg
  exact Encoding.impossible_of_certificates i g hg hm hu

spectrum_assert exclusion_of_unsat complete
end Spectrum.E467.OrderSixteen
