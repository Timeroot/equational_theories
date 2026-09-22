import equational_theories.Spectrum.SemisymmetricLoop

/-! # Mendelsohn and loop constructions for E115 and E481 -/

namespace Spectrum

theorem Mendelsohn.equation115 {Q : Type*} (M : Mendelsohn Q) :
    @Equation115 Q M.magma := by
  intro x y
  change x = M.op y (M.op (M.op x x) y)
  rw [M.idem, M.semi]

theorem SemisymmetricLoop.equation481 {Q : Type*} (L : SemisymmetricLoop Q) :
    @Equation481 Q L.magma := by
  intro x y z
  change x = L.op y (L.op x (L.op y (L.op z z)))
  rw [L.square, L.right_unit, L.semi]

theorem mendelsohn_115 : residues 3 {0, 1} {6} ⊆ Law115.spectrum := by
  intro n hn
  obtain ⟨M,hM⟩ := models_66 hn
  let D := @Mendelsohn.ofEquation66 (Fin n) M ((@Law66.models_iff _ M).mp hM)
  exact ⟨hn.1, D.magma, (@Law115.models_iff _ D.magma).mpr D.equation115⟩

theorem loops_481 : residues 3 {1, 2} {7} ⊆ Law481.spectrum := by
  intro n hn
  obtain ⟨M,hM⟩ := models_887 hn
  let L := @SemisymmetricLoop.ofEquation887 (Fin n) _ M
    ((@Law887.models_iff _ M).mp hM) ⟨0,hn.1⟩
  exact ⟨hn.1, L.magma, (@Law481.models_iff _ L.magma).mpr L.equation481⟩

end Spectrum
