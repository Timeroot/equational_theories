import equational_theories.Spectrum.Equation1083_1286.DesignWitnesses

/-! Prime-field seeds retained by the earlier survey, now checked in Lean.
Each proof checks two scalar coefficients, not all pairs of field elements.
Source recipes: data/spectrum/open_survey_20260927.json. -/

namespace Spectrum.E1083E1286.PrimeSeeds
open Law Law.MagmaLaw

theorem model_1083_19 : Law1083.HasModel 19 :=
  (scalar_model (which := false) (n := 19) 6 14 (by decide) (by decide)).hasModel
spectrum_assert model_1083_19 complete

theorem model_1083_23 : Law1083.HasModel 23 :=
  (scalar_model (which := false) (n := 23) 6 19 (by decide) (by decide)).hasModel
spectrum_assert model_1083_23 complete

theorem model_1083_29 : Law1083.HasModel 29 :=
  (scalar_model (which := false) (n := 29) 19 3 (by decide) (by decide)).hasModel
spectrum_assert model_1083_29 complete

theorem model_1083_31 : Law1083.HasModel 31 :=
  (scalar_model (which := false) (n := 31) 5 30 (by decide) (by decide)).hasModel
spectrum_assert model_1083_31 complete

theorem model_1083_37 : Law1083.HasModel 37 :=
  (scalar_model (which := false) (n := 37) 3 12 (by decide) (by decide)).hasModel
spectrum_assert model_1083_37 complete

theorem model_1083_43 : Law1083.HasModel 43 :=
  (scalar_model (which := false) (n := 43) 3 41 (by decide) (by decide)).hasModel
spectrum_assert model_1083_43 complete

theorem model_1083_47 : Law1083.HasModel 47 :=
  (scalar_model (which := false) (n := 47) 18 13 (by decide) (by decide)).hasModel
spectrum_assert model_1083_47 complete

theorem model_1083_53 : Law1083.HasModel 53 :=
  (scalar_model (which := false) (n := 53) 28 17 (by decide) (by decide)).hasModel
spectrum_assert model_1083_53 complete

theorem model_1083_61 : Law1083.HasModel 61 :=
  (scalar_model (which := false) (n := 61) 13 60 (by decide) (by decide)).hasModel
spectrum_assert model_1083_61 complete

theorem model_1083_67 : Law1083.HasModel 67 :=
  (scalar_model (which := false) (n := 67) 23 45 (by decide) (by decide)).hasModel
spectrum_assert model_1083_67 complete

theorem model_1083_73 : Law1083.HasModel 73 :=
  (scalar_model (which := false) (n := 73) 8 72 (by decide) (by decide)).hasModel
spectrum_assert model_1083_73 complete

theorem model_1083_79 : Law1083.HasModel 79 :=
  (scalar_model (which := false) (n := 79) 23 78 (by decide) (by decide)).hasModel
spectrum_assert model_1083_79 complete

theorem model_1286_19 : Law1286.HasModel 19 :=
  (scalar_model (which := true) (n := 19) 6 14 (by decide) (by decide)).hasModel
spectrum_assert model_1286_19 complete

theorem model_1286_23 : Law1286.HasModel 23 :=
  (scalar_model (which := true) (n := 23) 7 2 (by decide) (by decide)).hasModel
spectrum_assert model_1286_23 complete

theorem model_1286_29 : Law1286.HasModel 29 :=
  (scalar_model (which := true) (n := 29) 20 27 (by decide) (by decide)).hasModel
spectrum_assert model_1286_29 complete

theorem model_1286_31 : Law1286.HasModel 31 :=
  (scalar_model (which := true) (n := 31) 8 24 (by decide) (by decide)).hasModel
spectrum_assert model_1286_31 complete

theorem model_1286_37 : Law1286.HasModel 37 :=
  (scalar_model (which := true) (n := 37) 13 19 (by decide) (by decide)).hasModel
spectrum_assert model_1286_37 complete

theorem model_1286_43 : Law1286.HasModel 43 :=
  (scalar_model (which := true) (n := 43) 3 41 (by decide) (by decide)).hasModel
spectrum_assert model_1286_43 complete

theorem model_1286_47 : Law1286.HasModel 47 :=
  (scalar_model (which := true) (n := 47) 3 18 (by decide) (by decide)).hasModel
spectrum_assert model_1286_47 complete

theorem model_1286_53 : Law1286.HasModel 53 :=
  (scalar_model (which := true) (n := 53) 21 19 (by decide) (by decide)).hasModel
spectrum_assert model_1286_53 complete

theorem model_1286_59 : Law1286.HasModel 59 :=
  (scalar_model (which := true) (n := 59) 22 32 (by decide) (by decide)).hasModel
spectrum_assert model_1286_59 complete

theorem model_1286_67 : Law1286.HasModel 67 :=
  (scalar_model (which := true) (n := 67) 23 45 (by decide) (by decide)).hasModel
spectrum_assert model_1286_67 complete

theorem model_1286_71 : Law1286.HasModel 71 :=
  (scalar_model (which := true) (n := 71) 19 30 (by decide) (by decide)).hasModel
spectrum_assert model_1286_71 complete

theorem model_1286_73 : Law1286.HasModel 73 :=
  (scalar_model (which := true) (n := 73) 15 59 (by decide) (by decide)).hasModel
spectrum_assert model_1286_73 complete

theorem model_1286_79 : Law1286.HasModel 79 :=
  (scalar_model (which := true) (n := 79) 13 60 (by decide) (by decide)).hasModel
spectrum_assert model_1286_79 complete

end Spectrum.E1083E1286.PrimeSeeds
