import equational_theories.Spectrum.SemisymmetricLoop

/-! # Mendelsohn and loop constructions for related laws -/

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


theorem SemisymmetricLoop.equation667 {Q : Type*} (L : SemisymmetricLoop Q) :
    @Equation667 Q L.magma := by
  intro x y
  change x = L.op y (L.op x (L.op (L.op x x) y))
  rw [L.square, L.left_unit, L.semi]

theorem SemisymmetricLoop.equation883 {Q : Type*} (L : SemisymmetricLoop Q) :
    @Equation883 Q L.magma := by
  intro x y
  change x = L.op y (L.op (L.op x y) (L.op y y))
  rw [L.square, L.right_unit, L.semi]

theorem Mendelsohn.equation1719 {Q : Type*} (M : Mendelsohn Q) :
    @Equation1719 Q M.magma := by
  intro x y
  change x = M.op (M.op y y) (M.op (M.op x x) y)
  rw [M.idem, M.idem, M.semi]

theorem loops_667 : residues 3 {1, 2} {7} ⊆ Law667.spectrum := by
  intro n hn
  obtain ⟨M,hM⟩ := models_887 hn
  let L := @SemisymmetricLoop.ofEquation887 (Fin n) _ M
    ((@Law887.models_iff _ M).mp hM) ⟨0,hn.1⟩
  exact ⟨hn.1, L.magma, (@Law667.models_iff _ L.magma).mpr L.equation667⟩

theorem loops_883 : residues 3 {1, 2} {7} ⊆ Law883.spectrum := by
  intro n hn
  obtain ⟨M,hM⟩ := models_887 hn
  let L := @SemisymmetricLoop.ofEquation887 (Fin n) _ M
    ((@Law887.models_iff _ M).mp hM) ⟨0,hn.1⟩
  exact ⟨hn.1, L.magma, (@Law883.models_iff _ L.magma).mpr L.equation883⟩

theorem mendelsohn_1719 : residues 3 {0, 1} {6} ⊆ Law1719.spectrum := by
  intro n hn
  obtain ⟨M,hM⟩ := models_66 hn
  let D := @Mendelsohn.ofEquation66 (Fin n) M ((@Law66.models_iff _ M).mp hM)
  exact ⟨hn.1, D.magma, (@Law1719.models_iff _ D.magma).mpr D.equation1719⟩

spectrum_assert loops_667 complete
spectrum_assert loops_883 complete
spectrum_assert mendelsohn_1719 complete

end Spectrum
