import equational_theories.Spectrum.Basic
import equational_theories.Definability.FiniteFlavour

/-!
All definability relations imply inclusion of finite spectra. Only existence of the
new operation on the same carrier is used; definability of its graph is unnecessary here.
The finite versions are enough, so finite-only constructions propagate spectra too.
-/

namespace Law.MagmaLaw

variable {α : Type*} {L K : MagmaLaw α}

theorem subspectral_of_definableFin (h : K.DefinableFromFin L) : L.Subspectral K := by
  rw [subspectral_iff_hasModel]
  rintro n ⟨M, hM⟩
  obtain ⟨N, hN, _⟩ := h M hM
  exact ⟨N, hN⟩

theorem subspectral_of_termDefinableFin (h : K.TermDefinableFromFin L) : L.Subspectral K :=
  subspectral_of_definableFin (definableFin_of_termDefinableFin h)

theorem subspectral_of_structuralFin (h : K.StructuralFromFin L) : L.Subspectral K :=
  subspectral_of_definableFin (definableFin_of_structuralFin h)

theorem subspectral_of_termStructuralFin (h : K.TermStructuralFromFin L) : L.Subspectral K :=
  subspectral_of_termDefinableFin (termDefinableFin_of_termStructuralFin h)

theorem subspectral_of_definable (h : K.DefinableFrom L) : L.Subspectral K :=
  subspectral_of_definableFin (definableFin_of_definable h)

theorem subspectral_of_termDefinable (h : K.TermDefinableFrom L) : L.Subspectral K :=
  subspectral_of_termDefinableFin (termDefinableFin_of_termDefinable h)

theorem subspectral_of_structural (h : K.StructuralFrom L) : L.Subspectral K :=
  subspectral_of_structuralFin (structuralFin_of_structural h)

theorem subspectral_of_termStructural (h : K.TermStructuralFrom L) : L.Subspectral K :=
  subspectral_of_termStructuralFin (termStructuralFin_of_termStructural h)

end Law.MagmaLaw
