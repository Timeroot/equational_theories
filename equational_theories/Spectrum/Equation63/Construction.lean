import equational_theories.Spectrum.Equation63.CyclicDesign
import equational_theories.Spectrum.Equation63.Seeds
import equational_theories.Spectrum.Equation63.Designs.N9
import equational_theories.Spectrum.Equation63.Designs.N25
import equational_theories.Spectrum.Equation63.Designs.N27
import equational_theories.Spectrum.Equation63.Designs.N36

/-! The construction rules used by the finite certificate and the cofinite induction. -/
namespace Spectrum.E63
open Law Law.MagmaLaw

theorem seven {q r : ℕ} (hq : 0 < q) (hc : q.Coprime 60) (hr : r ≤ q)
    (g : Law63.HasModel q) (h : Law63.HasModel r) : Law63.HasModel (7*q+r) := by
  letI : NeZero q := ⟨by omega⟩
  exact ((designZMod q hc).relabel (ZMod.finEquiv q).toEquiv.symm).models hr g h idem7 idem8

theorem model70 : Law63.HasModel 70 :=
  Design9.design.models (by decide) (pointed3.mul pointed3).hasModel idem7.hasModel idem7 idem8

theorem model71 : Law63.HasModel 71 :=
  Design9.design.models (by decide) (pointed3.mul pointed3).hasModel idem8.hasModel idem7 idem8

theorem model179 : Law63.HasModel 179 :=
  Design25.design.models (by decide) (pointed5.mul pointed5).hasModel pointed4.hasModel idem7 idem8

theorem model190 : Law63.HasModel 190 :=
  Design27.design.models (by decide) ((pointed3.mul pointed3).mul pointed3).hasModel
    Law63.hasModel_one idem7 idem8

theorem model194 : Law63.HasModel 194 :=
  Design25.design.models (by decide) (pointed5.mul pointed5).hasModel idem19.hasModel idem7 idem8

theorem model197 : Law63.HasModel 197 :=
  Design27.design.models (by decide) ((pointed3.mul pointed3).mul pointed3).hasModel
    idem8.hasModel idem7 idem8

theorem model202 : Law63.HasModel 202 :=
  Design27.design.models (by decide) ((pointed3.mul pointed3).mul pointed3).hasModel
    (modular 13 3 (by decide)) idem7 idem8

theorem model257 : Law63.HasModel 257 :=
  Design36.design.models (by decide) (pointed4.mul (pointed3.mul pointed3)).hasModel
    idem5.hasModel idem7 idem8

theorem model269 : Law63.HasModel 269 :=
  Design36.design.models (by decide) (pointed4.mul (pointed3.mul pointed3)).hasModel
    (modular 17 12 (by decide)) idem7 idem8

end Spectrum.E63
