import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch00
import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch01
import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch02
import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch03
import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch04
import equational_theories.Spectrum.Equation667Twelve.Certificates.Batch05

namespace Spectrum.E667.Twelve
theorem rows_refuted : ∀ i ∈ collisionRows,
    ∀ f : Fin 12 → Fin 12 → Fin 12, RightIdentityTwelve.Holds f →
      (∀ y, f 0 y = FixedSquare.Cases.table i y) → False := by
  intro i hi f hf hr
  simp only [collisionRows, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_fixed_row 0 Certificates.C_row000.unsat f hf hr
  · exact no_fixed_row 1 Certificates.C_row001.unsat f hf hr
  · exact no_fixed_row 2 Certificates.C_row002.unsat f hf hr
  · exact no_fixed_row 3 Certificates.C_row003.unsat f hf hr
  · exact no_fixed_row 4 Certificates.C_row004.unsat f hf hr
  · exact no_fixed_row 5 Certificates.C_row005.unsat f hf hr
  · exact no_fixed_row 6 Certificates.C_row006.unsat f hf hr
  · exact no_fixed_row 7 Certificates.C_row007.unsat f hf hr
  · exact no_fixed_row 8 Certificates.C_row008.unsat f hf hr
  · exact no_fixed_row 9 Certificates.C_row009.unsat f hf hr
  · exact no_fixed_row 10 Certificates.C_row010.unsat f hf hr
  · exact no_fixed_row 11 Certificates.C_row011.unsat f hf hr
  · exact no_fixed_row 12 Certificates.C_row012.unsat f hf hr
  · exact no_fixed_row 13 Certificates.C_row013.unsat f hf hr
  · exact no_fixed_row 14 Certificates.C_row014.unsat f hf hr
  · exact no_fixed_row 15 Certificates.C_row015.unsat f hf hr
  · exact no_fixed_row 16 Certificates.C_row016.unsat f hf hr
  · exact no_fixed_row 17 Certificates.C_row017.unsat f hf hr
  · exact no_fixed_row 18 Certificates.C_row018.unsat f hf hr
  · exact no_fixed_row 19 Certificates.C_row019.unsat f hf hr
  · exact no_fixed_row 20 Certificates.C_row020.unsat f hf hr
  · exact no_fixed_row 21 Certificates.C_row021.unsat f hf hr
  · exact no_fixed_row 22 Certificates.C_row022.unsat f hf hr
  · exact no_fixed_row 23 Certificates.C_row023.unsat f hf hr
  · exact no_fixed_row 24 Certificates.C_row024.unsat f hf hr
  · exact no_fixed_row 25 Certificates.C_row025.unsat f hf hr
  · exact no_fixed_row 26 Certificates.C_row026.unsat f hf hr
  · exact no_fixed_row 27 Certificates.C_row027.unsat f hf hr
  · exact no_fixed_row 28 Certificates.C_row028.unsat f hf hr
  · exact no_fixed_row 29 Certificates.C_row029.unsat f hf hr
  · exact no_fixed_row 30 Certificates.C_row030.unsat f hf hr
  · exact no_fixed_row 31 Certificates.C_row031.unsat f hf hr
  · exact no_fixed_row 32 Certificates.C_row032.unsat f hf hr
  · exact no_fixed_row 33 Certificates.C_row033.unsat f hf hr
  · exact no_fixed_row 34 Certificates.C_row034.unsat f hf hr
  · exact no_fixed_row 35 Certificates.C_row035.unsat f hf hr
  · exact no_fixed_row 36 Certificates.C_row036.unsat f hf hr
  · exact RowReduction.no_fixed_row 37 Certificates.C_row037.unsat
      Certificates.C_three.unsat Certificates.C_four.unsat f hf hr
  · exact RowReduction.no_fixed_row 38 Certificates.C_row038.unsat
      Certificates.C_three.unsat Certificates.C_four.unsat f hf hr
  · exact RowReduction.no_fixed_row 39 Certificates.C_row039.unsat
      Certificates.C_three.unsat Certificates.C_four.unsat f hf hr
  · exact RowReduction.no_fixed_row 40 Certificates.C_row040.unsat
      Certificates.C_three.unsat Certificates.C_four.unsat f hf hr
  · exact RowReduction.no_fixed_row 41 Certificates.C_row041.unsat
      Certificates.C_three.unsat Certificates.C_four.unsat f hf hr
  · exact no_fixed_row 42 Certificates.C_row042.unsat f hf hr
  · exact no_fixed_row 43 Certificates.C_row043.unsat f hf hr
  · exact no_fixed_row 44 Certificates.C_row044.unsat f hf hr
  · exact no_fixed_row 45 Certificates.C_row045.unsat f hf hr
  · exact no_fixed_row 46 Certificates.C_row046.unsat f hf hr
  · exact no_fixed_row 47 Certificates.C_row047.unsat f hf hr
  · exact no_fixed_row 48 Certificates.C_row048.unsat f hf hr
  · exact no_fixed_row 49 Certificates.C_row049.unsat f hf hr

theorem three_refuted : threeFormula.Unsat := Certificates.C_three.unsat
theorem four_refuted : fourFormula.Unsat := Certificates.C_four.unsat

theorem no_idempotent_collision
    (f : Fin 12 → Fin 12 → Fin 12) (h : RightIdentityTwelve.Holds f)
    (he : f 0 0 = 0) (x : Fin 12) (hx : x ≠ 0) (hs : f x x = 0) : False := by
  obtain ⟨i,hi,g,hg,hr⟩ := normalize_idempotent_collision f h he x hx hs
  exact rows_refuted i hi g hg hr

spectrum_assert rows_refuted complete
spectrum_assert three_refuted complete
spectrum_assert four_refuted complete
spectrum_assert no_idempotent_collision complete
end Spectrum.E667.Twelve
